


(* 
Step 1: Grab all concrete calls (i.e. in function calls $func(32) or dependent types (uN(32))). Put it in the environment.
Step 2: On a second pass, go through all inductive definitions, relations and function definitions:
  - for family types, special care is needed to remove the dependent typing so this will be done separately. (Skip for now)
  - For inductive types, make a fresh inductive type with the corresponding concrete type. Resolve any premises if possible. 
    Propagate this change to the location of the function call.
*)


open Il.Ast
open Il.Print

open Il.Eval
open Util.Source
open Util.Error


(* Env Creation and utility functions *)

module StringMap = Map.Make(String)
module IdSet = Set.Make(String)

module ExpSet = Set.Make(struct
  type t = Il.Ast.exp
  let compare exp1 exp2 = if Il.Eq.eq_exp exp1 exp2 then 0 else String.compare (string_of_exp exp1) (string_of_exp exp2) (* HACK - Need better way to compare expressions, only hurts performance *)
end
)

module TypSet = Set.Make(struct
  type t = Il.Ast.typ
  let compare typ1 typ2 = if Il.Eq.eq_typ typ1 typ2 then 0 else String.compare (string_of_typ typ1) (string_of_typ typ2) (* HACK - Need better way to compare types, only hurts performance *)
end
)

type monoenv = 
{
  mutable calls: (ExpSet.t ref) StringMap.t;
  mutable concrete_dependent_types: (TypSet.t ref) StringMap.t;
  mutable il_env: env;
}

let new_env() = 
{
    calls = StringMap.empty;
    concrete_dependent_types = StringMap.empty;
    il_env = Il.Env.empty;
}

let mono = "Monomorphization"

let print_env (m_env : monoenv) = 
  print_endline "Printing the Env: ";
  print_endline " ";

  StringMap.iter (fun id exps -> 
    print_string ("Set with key " ^ id ^ "{");
    print_string (String.concat ", " (List.map string_of_exp (ExpSet.elements !exps)));
    print_endline "}") m_env.calls;

  StringMap.iter (fun id typs -> 
    print_string ("Set with key " ^ id ^ "{");
    print_string (String.concat ", " (List.map string_of_typ (TypSet.elements !typs)));
    print_endline "}") m_env.concrete_dependent_types

(* let bind_exp m_env' id e =
  if id = "_" then m_env' else
    match StringMap.find_opt id m_env' with 
      | None -> StringMap.add id (ref (ExpSet.singleton e)) m_env'
      | Some set -> set := ExpSet.add e !set; m_env' *)

let bind_typ m_env' id t =
  if id = "_" then m_env' else
    match StringMap.find_opt id m_env' with 
      | None -> StringMap.add id (ref (TypSet.singleton t)) m_env'
      | Some set -> set := TypSet.add t !set; m_env'

let concrete_dep_types_bind m_env id t =
  m_env.concrete_dependent_types <- bind_typ m_env.concrete_dependent_types id t

let transform_atom (a : atom) = 
  match a.it with
    | Atom s -> s
    | _ -> ""

let is_atomid (a : atom) =
  match a.it with
    | Atom _ -> true
    | _ -> false

    
let to_string_mixop (m : mixop) = match m with
  | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> a
  | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )

let rec subst_and_reduce_prems (m_env : monoenv) (subst : subst) (prem : prem): prem = 
  match prem.it with
    | IfPr exp -> IfPr (Il.Eval.reduce_exp m_env.il_env (Il.Subst.subst_exp subst exp)) $ prem.at
    | IterPr (p, _) -> subst_and_reduce_prems m_env subst p
    | _ -> prem

(* Checking the existance of dependent types in a function argument list *)

(* let rec get_var_exp (exp : exp) : string list = 
  match exp.it with
    | VarE id -> [id.it]
    | TupE exps -> List.concat_map get_var_exp exps
    | CaseE (_, e) -> get_var_exp e
    | _ -> []

and get_var_typ (typ : typ) : string list =
  match typ.it with
    | VarT (_, args) -> List.concat_map get_var_arg args 
    | TupT exp_typ_pairs -> List.concat_map (fun (_, t) -> get_var_typ t) exp_typ_pairs
    | IterT (t, _) -> get_var_typ t
    | _ -> []

and get_var_arg (arg : arg) : string list =
  match arg.it with
    | ExpA exp -> get_var_exp exp
    | TypA typ -> get_var_typ typ
    | _ -> []

let rec check_dependent_types (arglist : arg list) (return_type : typ) : int list = 
  let rec f n arglist = 
    match arglist with
      | [] -> []
      | arg :: args -> let ids_used = get_var_typ return_type @ List.concat_map get_var_arg args |> IdSet.of_list in
        (if List.filter (fun a -> IdSet.mem a ids_used) (get_var_arg arg) <> [] 
          then [n]
          else []) @ f (n + 1) args in
  f 0 arglist  *)


(* Checking the existance of parametric types in a call argument list *)

(* let get_param_id_typ (typ : typ) : string  =
  match typ.it with
    | VarT (id, _) -> id.it
    | _ -> ""

let get_param_id_arg (arg : arg) : string =
  match arg.it with
    | TypA typ -> get_param_id_typ typ
    | _ -> ""

let check_parametric_types (arglist : arg list) : int list = 
  let rec f n arglist = 
    match arglist with
      | [] -> []
      | arg :: args -> 
        (if (get_param_id_arg arg) <> ""
          then [n]
          else []) @ f (n + 1) args in
  f 0 arglist  *)

(* String transformation Args *)

let rec to_string_exp (exp : exp) : string = 
  match exp.it with
    | BoolE _ | NumE _ | TextE _ -> string_of_exp exp
    | ListE exps -> "l" ^ String.concat "_" (List.map to_string_exp exps) 
    | TupE exps -> "t" ^ String.concat "_" (List.map to_string_exp exps) 
    | CaseE (mixop, exp) -> to_string_mixop mixop ^ "_" ^ to_string_exp exp
    | CvtE (e, _, _) -> to_string_exp e
    | SubE (e, _, _) -> to_string_exp e
    | _ -> error exp.at mono "Cannot transform these into strings"

and to_string_typ (typ : typ) : string = 
  match typ.it with
    | BoolT | NumT _ | TextT -> string_of_typ typ
    | VarT (id, args) -> id.it ^ "_" ^ String.concat "__" (List.map to_string_arg args)
    | IterT (typ, iter) -> string_of_typ typ ^ "_" ^ string_of_iter iter
    | TupT exp_typ_pairs -> "tt" ^ String.concat "_" (List.map (fun (e, t) -> to_string_exp e ^ to_string_typ t) exp_typ_pairs) 

and to_string_arg (arg : arg): string =
  match arg.it with
    | ExpA exp -> to_string_exp exp
    | TypA typ -> to_string_typ typ
    | _ -> ""

and transform_id (id : id) (args : arg list): id =
  id.it ^ "_mono_" ^ String.concat "__" (List.map to_string_arg args) $ id.at

let create_args_pairings (args_ids : id list) (concrete_args : arg list): subst =
  List.fold_left (fun acc (id, arg) -> match arg.it with
    | ExpA exp -> Il.Subst.add_varid acc id exp
    | TypA typ -> Il.Subst.add_typid acc id typ
    | DefA x -> Il.Subst.add_defid acc id x
    | GramA g -> Il.Subst.add_gramid acc id g) Il.Subst.empty (List.combine args_ids concrete_args)

let replace_args (subst : subst) (args: arg list): arg list =
  Il.Subst.subst_args subst args

let evaluate_args (m_env : monoenv) (args : arg list): arg list =
  List.map (fun arg -> reduce_arg m_env.il_env arg) args

(* Terminal cases traversal *)

let rec check_reducible_exp (exp : exp) : bool =
  match exp.it with
    | BoolE _ | NumE _ | TextE _ -> true
    | UnE (_, _, e) -> check_reducible_exp e
    | BinE (_, _, e1, e2) -> check_reducible_exp e1 && check_reducible_exp e2
    | CmpE (_, _, e1, e2) -> check_reducible_exp e1 && check_reducible_exp e2
    | TupE exps -> List.fold_left (fun acc e -> acc && check_reducible_exp e) true exps 
    | CvtE (e, _, _) -> check_reducible_exp e
    | SubE (e, _, _) -> check_reducible_exp e
    | ListE exps -> List.fold_left (fun acc e -> acc && check_reducible_exp e) true exps 
    | CaseE (_, e) -> check_reducible_exp e
    | _ -> false

and check_reducible_typ (typ: typ): bool =
  match typ.it with
    | IterT (t, _iter) -> check_reducible_typ t
    | VarT (_, args) -> check_reducible_args args
    | TupT exp_typ_pairs -> List.fold_left (fun acc (_e, t) -> acc && check_reducible_typ t) true exp_typ_pairs
    | _ -> true

and check_reducible_arg (arg: arg): bool =
  match arg.it with
    | TypA typ -> check_reducible_typ typ
    | ExpA exp -> check_reducible_exp exp
    | _ -> false

and check_reducible_args (args: arg list): bool =
  List.fold_left (fun acc arg -> acc && check_reducible_arg arg) true args

(* Monomorphization Pass *)

let get_dependent_type_args (typ : typ) = 
  match typ.it with  
    | VarT (_, concrete_args) -> concrete_args
    | _ -> error typ.at mono "Applied monomorphization on a non-concrete dependent type"

let get_variables_from_arg (arg : arg): id = 
  match arg.it with
    | ExpA ({it = VarE id; _}) -> id
    | TypA ({it = VarT (id, _); _}) -> id
    | _ -> error arg.at mono "Arguments on LHS have something other than id"
  
let rec transform_dependent_type (m_env : monoenv) (typ : typ) (subst: subst): typ = 
  (match typ.it with
    | VarT (id, args) when args <> [] -> 
      let args_replaced = replace_args subst args in
      if check_reducible_args args_replaced 
        then 
          let args_evaluated = evaluate_args m_env args_replaced in
          concrete_dep_types_bind m_env id.it (VarT(id, args_evaluated) $ typ.at); 
          VarT (transform_id id args_evaluated, []) 
        else typ.it
          (* else error typ.at mono "Cannot monomorphize correctly" *)
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (e, transform_dependent_type m_env t subst)) exp_typ_pairs)
    | IterT (t, iter) -> IterT (transform_dependent_type m_env t subst, iter)
    | t -> t
  ) $ typ.at

let transform_bind (m_env : monoenv) (subst : subst) (bind : bind) : bind =
  (match bind.it with
    | ExpB (id, typ) -> ExpB(id, transform_dependent_type m_env typ subst)
    | b -> b) $ bind.at

let transform_type_creation (m_env : monoenv) (id : id) (inst : inst) (at : Util.Source.region) : def list =
  match inst.it with 
    | InstD (binds, args, deftyp) -> (match deftyp.it with 
      | AliasT typ -> (match StringMap.find_opt id.it m_env.concrete_dependent_types with
        | None -> let new_deftyp = AliasT (transform_dependent_type m_env typ Il.Subst.empty) $ deftyp.at in 
          [(TypD (id, [], [InstD (binds, [], new_deftyp) $ inst.at]) $ at)]
        | Some set_ref -> 
          List.map ( fun t -> 
            let dep_args = get_dependent_type_args t in 
            let args_ids = List.map get_variables_from_arg args in  
            let subst = create_args_pairings args_ids dep_args in
            let new_deftyp = AliasT (transform_dependent_type m_env typ subst) $ deftyp.at in 
            TypD (transform_id id dep_args, [], [InstD ([], [], new_deftyp) $ inst.at]) $ at
            ) (TypSet.elements !set_ref)  
      )
      | StructT typfields -> (
        let new_deftyp = StructT (List.map (fun (a, (bs, t, prems), hints) -> (a, (bs, transform_dependent_type m_env t Il.Subst.empty, prems), hints)) typfields) $ deftyp.at in
        [TypD (id, [], [InstD ([], [], new_deftyp) $ inst.at]) $ at] (* Ignore args for now, there shouldn't be any here *)
      )
      | VariantT typcases -> (match StringMap.find_opt id.it m_env.concrete_dependent_types with
        | None -> let new_deftyp = VariantT (List.map (fun (m, (bs, t, prems), hints) -> (m, (bs, transform_dependent_type m_env t Il.Subst.empty, prems), hints)) typcases) $ deftyp.at in
          [TypD (id, [], [InstD ([], [], new_deftyp) $ inst.at]) $ at] 
        | Some set_ref ->
          List.map ( fun t -> 
            let dep_args = get_dependent_type_args t in 
            let args_ids = List.map get_variables_from_arg args in  
            let subst = create_args_pairings args_ids dep_args in
            let new_deftyp = VariantT (List.map (fun (m, (bs, t, prems), hints) -> (m, (List.map (transform_bind m_env subst) bs, transform_dependent_type m_env t subst, List.map (subst_and_reduce_prems m_env subst) prems), hints)) typcases) $ deftyp.at in 
            TypD (transform_id id dep_args, [], [InstD ([], [], new_deftyp) $ inst.at]) $ at
            ) (TypSet.elements !set_ref)
      )
    )

let rec transform_def (m_env : monoenv) (def : def) : def list =
  match def.it with
    | TypD (id, _, [inst]) -> transform_type_creation m_env id inst def.at
    | TypD (_id, _params, _insts) -> [def] (* TODO: Ignore family types for now *)
    | RelD (_id, _mixop, _typ, _rules) -> [def]
    | DecD (_id, _params, _typ, _clauses) -> [def]
    | RecD defs -> List.concat_map (transform_def m_env) defs 
    | _ -> [def]    

(* Main transformation function *)
let transform (script: Il.Ast.script) =
  let m_env = new_env() in 
  m_env.il_env <- Il.Env.env_of_script script;
  (* Reverse the script in order to monomorphize nested ones correctly *)
  let transformed_script = List.rev (List.concat_map (transform_def m_env) (List.rev script)) in
  print_env m_env;
  transformed_script

