open Il.Ast
open Util.Source
open Il
open Util

(* Exception raised when a type has unbounded cases *)
exception UnboundedArg of string

module ExpSet = Set.Make(struct
  type t = Il.Ast.exp
  let compare exp1 exp2 = if Eq.eq_exp exp1 exp2 then 0
    (* HACK - Need better way to compare exps, only hurts performance *)
    else String.compare (Print.string_of_exp exp1) (Print.string_of_exp exp2)
end)

let _error at msg = Error.error at "Subtyping Removal" msg

let empty_tuple_exp at = TupE [] $$ at % (TupT [] $ at)

let rec check_recursive_type (id : id) (t : typ): bool =
  match t.it with
  | VarT (typ_id, _) -> id = typ_id
  | IterT (typ, _iter) -> check_recursive_type id typ
  | TupT exp_typ_pairs -> List.exists (fun (_, typ) -> check_recursive_type id typ) exp_typ_pairs
  | _ -> false

(* Computes the cartesian product of a given list. *)
let product_of_lists (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> v :: existing) lst) acc) [[]] lists

let product_of_lists_append (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> existing @ [v]) lst) acc) [[]] lists

let check_matching env (call_args : arg list) (match_args : arg list) = 
  Option.is_some (try Il.Eval.match_list Il.Eval.match_arg env Il.Subst.empty call_args match_args with Il.Eval.Irred -> None)

let rec get_all_case_instances env (var_id : id) (concrete_args : arg list) (inst : inst): exp' list =
  match inst.it with
  | InstD (_, args, deftyp) -> 
    let subst = Option.value (try Il.Eval.match_list Il.Eval.match_arg env Il.Subst.empty concrete_args args with Il.Eval.Irred -> None) ~default:Il.Subst.empty in
    let new_deftyp = Il.Subst.subst_deftyp subst deftyp in
    match new_deftyp.it with
    | AliasT typ -> get_all_case_instances_from_typ env typ
    | StructT _typfields -> []
    | VariantT typcases when List.for_all (fun (_, (_, t, _), _) -> t.it = TupT []) typcases -> 
      List.map (fun (m, _, _) -> CaseE(m, empty_tuple_exp no_region)) typcases
    | VariantT typcases -> 
      List.iter (fun (_, (_, t, _), _) -> 
        if check_recursive_type var_id t then raise (UnboundedArg (Print.string_of_typ t)) else () 
      ) typcases;
      List.concat_map (fun (m, (_, t, _), _) -> 
        let case_instances = get_all_case_instances_from_typ env t in
        List.map (fun e -> CaseE(m, e $$ t.at % t)) case_instances
      ) typcases 

and get_all_case_instances_from_typ env (typ: typ): exp' list  = 
  let apply_phrase t e = e $$ t.at % t in 
  match typ.it with
  | BoolT -> [BoolE false; BoolE true]
  | VarT(var_id, dep_args) -> let (_, insts) = Il.Env.find_typ env var_id in 
    (match insts with
    | [] -> [] (* Should never happen *)
    | _ -> match List.find_opt (fun inst -> match inst.it with | InstD (_, args, _) -> check_matching env dep_args args) insts with
      | None -> raise (UnboundedArg (Print.string_of_typ typ))
      | Some inst -> get_all_case_instances env var_id dep_args inst
    )
  | TupT exp_typ_pairs -> let instances_list = List.map (fun (_, t) -> List.map (apply_phrase t) (get_all_case_instances_from_typ env t)) exp_typ_pairs in
    List.map (fun exps -> TupE exps) (product_of_lists_append instances_list)
  | IterT (t, Opt) -> 
    let instances = get_all_case_instances_from_typ env t in
    OptE None :: List.map (fun e -> OptE (Some (apply_phrase t e))) instances
  (* | _ -> print_endline ("Encountered invalid type " ^ string_of_typ typ); [] *)
  | _ -> raise (UnboundedArg (Print.string_of_typ typ))

let collect_sub_matches env: (id * exp) list list ref * (module Iter.Arg) =
  let module Arg = 
    struct
      include Iter.Skip 
      let acc = ref []
      let visited = ref ExpSet.empty
      let visit_exp (exp : exp) = 
        match exp.it with
        | SubE ({it = VarE var_id; _} as e, t1, t2) when not (ExpSet.mem e !visited) ->
          visited := ExpSet.add e !visited; 
          let case_instances = (try get_all_case_instances_from_typ env t1 with
          | UnboundedArg msg -> 
            print_endline ("WARNING: UNBOUNDED Argument: " ^ msg);
            print_endline ("At: " ^ string_of_region exp.at);
            print_endline ("For type: " ^ Il.Print.string_of_typ t1);
            print_endline ("Coercing to: " ^ Il.Print.string_of_typ t2);
            []
          ) in
          acc := List.map (fun e' -> (var_id, e' $$ t1.at % t1)) case_instances :: !acc
        | _ -> ()
    end
  in Arg.acc, (module Arg)

let transform_clause _id env clause =
  match clause.it with 
  | DefD (binds, args, exp, prems) -> 
    let acc_cases, (module Arg: Iter.Arg) = collect_sub_matches env in
    let module Acc = Iter.Make(Arg) in
    Acc.args args;
    let cases_list = product_of_lists !acc_cases in
    let subst_list = List.map (List.fold_left (fun acc (id, exp) -> 
      Il.Subst.add_varid acc id exp) Il.Subst.empty
    ) cases_list in
    List.map (fun subst -> 
      let (new_binds, _) = Il.Subst.subst_binds subst binds in
      let new_args = Il.Subst.subst_args subst args in
      let new_prems = Il.Subst.subst_list Il.Subst.subst_prem subst prems in
      let new_exp = Il.Subst.subst_exp subst exp in
      DefD (new_binds, new_args, new_exp, new_prems) $ clause.at
    ) subst_list
  
let remove_overlapping_clauses env clauses = 
  Lib.List.nub (fun clause clause' -> match clause.it, clause'.it with
  | DefD (_, args, _, _), DefD (_, args', _, _) -> 
    (* Reduction is done here to remove subtyping expressions *)
    let reduced_args = List.map (Eval.reduce_arg env) args in
    let reduced_args' = List.map (Eval.reduce_arg env) args' in
    Eq.eq_list Eq.eq_arg reduced_args reduced_args'
  ) clauses

let rec transform_def env def = 
  (match def.it with
  | RecD defs -> RecD (List.map (transform_def env) defs)
  | DecD (id, params, typ, clauses) -> DecD (id, params, typ, List.concat_map (transform_clause id env) clauses |> (remove_overlapping_clauses env))
    | d -> d
  ) $ def.at

let transform (il : script): script = 
  let env = Env.env_of_script il in 
  List.map (transform_def env) il