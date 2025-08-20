(* TODO - Make sure we are applying the right regions at the right spots (necessary for debugging later) *)
(* TODO - Improve eval reduction function to reduce function calls correctly (can't have function calls with irreducible arguments actually be reduced) *)
open Il.Ast
open Il.Print
open Il
open Il.Eval
open Util.Source
open Util.Error
open Xl

(* Exception raised when a dependent type depends on unbounded arguments *)
exception UnboundedArg of string

(* Env Creation and utility functions *)

module StringMap = Map.Make(String)
module IdSet = Set.Make(String)

module ExpSet = Set.Make(struct
  type t = Il.Ast.exp
  let compare exp1 exp2 = if Il.Eq.eq_exp exp1 exp2 then 0 
    else String.compare (string_of_exp exp1) (string_of_exp exp2) (* HACK - Need better way to compare expressions, only hurts performance *)
end
)

module TypSet = Set.Make(struct
  type t = Il.Ast.typ
  let compare typ1 typ2 = if Il.Eq.eq_typ typ1 typ2 then 0 
    else String.compare (string_of_typ typ1) (string_of_typ typ2) (* HACK - Need better way to compare types, only hurts performance *)
end
)

type monoenv = 
{
  mutable calls: (ExpSet.t ref) StringMap.t;
  mutable concrete_dependent_types: (TypSet.t ref) StringMap.t;
  mutable il_env: env;
  mutable mono_list: def list;
}

let new_env = 
{
  calls = StringMap.empty;
  concrete_dependent_types = StringMap.empty;
  il_env = Il.Env.empty;
  mono_list = [];
}

let mono = "Monomorphization"

let empty_tuple_exp at = TupE [] $$ at % (TupT [] $ at)

let map_snd f = List.map (fun (v1, v2) -> (v1, f v2))

let msg_prefix = "Encountered an unbounded type: "


let _unbounded_error at msg = error at mono (msg_prefix ^ msg)

let print_env (m_env : monoenv) = 
  print_endline "Printing the Env: ";
  print_endline " ";

  print_endline "Function calls:";
  StringMap.iter (fun id exps -> 
    print_string ("Set with key " ^ id ^ "{");
    print_string (String.concat ", " (List.map string_of_exp (ExpSet.elements !exps)));
    print_endline "}") m_env.calls;
  
  print_endline "Dependent Types:";
  StringMap.iter (fun id typs -> 
    print_string ("Set with key " ^ id ^ "{");
    print_string (String.concat ", " (List.map string_of_typ (TypSet.elements !typs)));
    print_endline "}") m_env.concrete_dependent_types;
  
  print_endline "Mono funcs/deps:";
  List.iter (fun def -> print_endline (Il.Print.string_of_def def)) m_env.mono_list

let bind_typ m_env' id t =
  if id = "_" then m_env' else
    match StringMap.find_opt id m_env' with 
      | None -> StringMap.add id (ref (TypSet.singleton t)) m_env'
      | Some set -> set := TypSet.add t !set; m_env'

let bind_exp m_env' id t =
  if id = "_" then m_env' else
    match StringMap.find_opt id m_env' with 
      | None -> StringMap.add id (ref (ExpSet.singleton t)) m_env'
      | Some set -> set := ExpSet.add t !set; m_env'

let add_to_mono_list (m_env : monoenv) (def : def): unit =
  m_env.mono_list <- def :: m_env.mono_list 
      
let concrete_dep_types_bind m_env id t =
  m_env.concrete_dependent_types <- bind_typ m_env.concrete_dependent_types id t

let function_calls_bind m_env id t =
  m_env.calls <- bind_exp m_env.calls id t

let partition_mapi p l =
  let rec part left right i = function
  | [] -> (List.rev left, List.rev right)
  | x :: l ->
      begin match p x i with
        | Either.Left v -> part (v :: left) right (i + 1) l
        | Either.Right v -> part left (v :: right) (i + 1)  l
      end
  in
  part [] [] 0 l

let partition_map_using_tail p l =
  let rec part left right = function
  | [] -> (List.rev left, List.rev right)
  | x :: l ->
      begin match p x l with
        | Either.Left v -> part (v :: left) right l
        | Either.Right v -> part left (v :: right) l
      end
  in
  part [] [] l

let filter_map_using_taili f =
  let rec aux accu i = function
    | [] -> List.rev accu
    | x :: l ->
        match f x l i with
        | None -> aux accu (i + 1) l
        | Some v -> aux (v :: accu) (i + 1) l
  in
  aux [] 0

let map_bool_to_either (a: 'a) (b : bool): ('a, 'a) Either.t =
  if b then Either.Left a else Either.Right a

let map_bool_to_option (a: 'a) (b : bool): 'a option =
  if b then Some a else None

let reduce_arg (env : Il.Env.t) (arg : arg): arg = 
  (match arg.it with
    | ExpA exp -> ExpA (Il.Eval.reduce_exp env exp)
    | TypA typ -> TypA (Il.Eval.reduce_typ env typ)
    | a -> a
  ) $ arg.at
  
(* Computes the cartesian product of a given list. *)
let product_of_lists (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> v :: existing) lst) acc) [[]] lists

let product_of_lists_append (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> existing @ [v]) lst) acc) [[]] lists

let transform_atom (a : atom) = 
  match a.it with
    | Atom s -> s
    | _ -> ""

let is_atomid (a : atom) =
  match a.it with
    | Atom _ -> true
    | _ -> false

let is_type_arg (a : arg) = 
  match a.it with
    | TypA _ -> true
    | _ -> false

let is_type_param (p : param) =
  match p.it with
    | TypP _ -> true
    | _ -> false

(* String transformation functions *)

let to_string_mixop (m : mixop) = match m with
  | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> a
  | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )

let rec to_string_exp (exp : exp) : string = 
  match exp.it with
    | BoolE _ | NumE _ | TextE _ -> string_of_exp exp
    | ListE exps -> "l" ^ String.concat "_" (List.map to_string_exp exps) 
    | TupE [] -> ""
    | TupE exps -> String.concat "_" (List.map to_string_exp exps) 
    | CaseE (mixop, {it = TupE []; _}) -> to_string_mixop mixop 
    | CaseE (_mixop, exp) -> to_string_exp exp
    | CvtE (e, _, _) -> to_string_exp e
    | SubE (e, _, _) -> to_string_exp e
    (* | _ -> assert false *)
    | _ -> error exp.at mono ("Cannot transform " ^ string_of_exp exp ^ " into string")

and to_string_typ (typ : typ) : string = 
  match typ.it with
    | BoolT | NumT _ | TextT -> string_of_typ typ
    | VarT (id, args) -> id.it ^ "_" ^ String.concat "_" (List.map to_string_arg args)
    | IterT (typ, iter) -> string_of_typ typ ^ "_" ^ string_of_iter iter
    | TupT [] -> ""
    | TupT exp_typ_pairs -> "tt" ^ String.concat "_" (List.map (fun (e, t) -> to_string_exp e ^ to_string_typ t) exp_typ_pairs) 

and to_string_arg (arg : arg): string =
  match arg.it with
    | ExpA exp -> to_string_exp exp
    | TypA typ -> to_string_typ typ
    | _ -> ""

and transform_id_from_args (id : id) (args : arg list): id =
  if args = [] then id else 
  id.it ^ "_mono_" ^ String.concat "_" (List.map to_string_arg args) $ id.at

and transform_string_from_exps (text : string) (exps : exp list): string =
  if exps = [] then text else 
  text ^ "_mono_" ^ (String.concat "_" (List.map to_string_exp exps))

and transform_id_from_exps (m_env : monoenv) (id : id) (exps : exp list): id =
  transform_string_from_exps id.it (List.map (Il.Eval.reduce_exp m_env.il_env) exps) $ id.at

(* TODO fix this to remove the correct holes in the more complicated case *)
and transform_mixop (m_env : monoenv) (m : mixop) (num_kept : int) (exps : exp list) : mixop =
  if exps = [] then m else
  let reduced_exps = List.map (Il.Eval.reduce_exp m_env.il_env) exps in
  match m with
    | [{it = Atom.Atom a; _} as atom]::tail when List.for_all ((=) []) tail -> 
      [Atom.Atom (transform_string_from_exps a reduced_exps) $$ atom.at % atom.note]::(List.init num_kept (fun _ -> []))
    | _ -> 
      let rec aux num_empty = function
        | [] -> []
        | [] :: ls when num_empty > num_kept -> aux (num_empty + 1) ls
        | [] :: ls -> [] :: aux (num_empty + 1) ls
        | _ :: ls -> aux num_empty ls
      in
      List.mapi (fun i atoms -> 
      let length_last = List.length m in 
      let new_atom = Atom.Atom (transform_string_from_exps "" reduced_exps) $$ (no_region, Atom.info "") in
      if i = length_last - 1 then atoms @ [new_atom] else atoms) (aux 0 m)

let create_args_pairings (args_ids : id list) (concrete_args : arg list): subst =
  List.fold_left (fun acc (id, arg) -> 
    if id.it = "_" then acc else
    match arg.it with
    | ExpA exp -> Il.Subst.add_varid acc id exp
    | TypA typ -> Il.Subst.add_typid acc id typ
    | DefA x -> Il.Subst.add_defid acc id x
    | GramA g -> Il.Subst.add_gramid acc id g) Il.Subst.empty (List.combine args_ids concrete_args)

(* Simple getters which traverse part of the AST *)

let get_dependent_type_args (typ : typ): arg list = 
  match typ.it with  
    | VarT (_, concrete_args) -> concrete_args
    | _ -> error typ.at mono "Applied monomorphization on a non-concrete dependent type"

let get_function_call (exp : exp): id * arg list =
  match exp.it with
    | CallE (id, args) -> (id, args)
    | _ -> error exp.at mono "Applied monomorphization on a non-function call expression"

let rec get_variable_id_safe (exp : exp): id = 
  match exp.it with
    | VarE id -> id
    | IterE (e, _) -> get_variable_id_safe e
    | SubE (e, _, _) -> get_variable_id_safe e
    | _ -> "" $ no_region

let get_variable_id_from_param (param : param): id =
  match param.it with
    | ExpP (id, _) -> id
    | TypP id -> id
    | DefP (id, _, _) -> id
    | GramP (id, _) -> id

let get_tuple_from_type (typ : typ): ((exp * typ) list) option =
  match typ.it with
    | TupT [] -> None
    | TupT e_t -> Some e_t
    | _ -> None (* We don't need to worry about the case of it being single typed *)
  
let rec transform_exp (m_env : monoenv) (subst : subst) (exp : exp): exp =
  let t_func = transform_exp m_env subst in
  (match exp.it with
    | UnE (unop, optyp, e) -> UnE (unop, optyp, t_func e)
    | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2)
    | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2)
    | TupE exps -> TupE (List.map t_func exps)
    | ProjE (e, i) -> ProjE (t_func e, i)
    | CaseE (m, e) -> CaseE (m, t_func e) 
    | UncaseE (e, m) -> UncaseE (t_func e, m)
    | OptE (Some e) -> OptE (Some (t_func e))
    | TheE e -> TheE (t_func e)
    | StrE expfields -> StrE (map_snd t_func expfields)
    | DotE (e, a) -> DotE (t_func e, a)
    | CompE (e1, e2) -> CompE (t_func e1, t_func e2)
    | ListE exps -> ListE (List.map t_func exps)
    | LiftE e -> LiftE (t_func e)
    | MemE (e1, e2) -> MemE (t_func e1, t_func e2)
    | LenE e -> LenE (t_func e)
    | CatE (e1, e2) -> CatE (t_func e1, t_func e2)
    | IdxE (e1, e2) -> IdxE (t_func e1, t_func e2)
    | SliceE (e1, e2, e3) -> SliceE (t_func e1, t_func e2, t_func e3)
    | UpdE (e1, path, e2) -> UpdE (t_func e1, transform_path m_env subst path, t_func e2)
    | ExtE (e1, path, e2) -> ExtE (t_func e1, transform_path m_env subst path, t_func e2)
    | CallE (id, args) ->
      let subst_args = List.map (transform_arg m_env subst) args in
      let (type_args, normal_args) = List.partition is_type_arg subst_args in
      if type_args <> []
      then (
        let new_id = transform_id_from_args id (List.map (reduce_arg m_env.il_env) type_args) in
        function_calls_bind m_env id.it (CallE (new_id, List.map (reduce_arg m_env.il_env) type_args) $$ exp.at % exp.note);
        CallE (new_id, normal_args)
        )
      else
        CallE (id, subst_args)
    | IterE (e, iterexp) -> IterE (t_func e, transform_iterexp m_env subst iterexp)
    | CvtE (e, ntyp1, ntyp2) -> CvtE (t_func e, ntyp1, ntyp2)
    | SubE (e, t1, t2) -> SubE (t_func e, transform_type m_env subst t1, transform_type m_env subst t2)
    | e -> e
  ) $$ exp.at % (transform_type m_env subst exp.note)

and transform_iterexp (m_env : monoenv) (subst : subst) (iterexp : iterexp): iterexp = 
  let (iter, id_exp_pairs) = iterexp in
  (transform_iter m_env subst iter, map_snd (transform_exp m_env subst) id_exp_pairs)

and transform_iter (m_env : monoenv) (subst : subst) (iter : iter): iter =
  match iter with 
    | ListN (e, id) -> ListN(transform_exp m_env subst e, id)
    | i -> i

and transform_path (m_env : monoenv) (subst : subst) (path : path): path = 
  (match path.it with
    | RootP -> RootP
    | IdxP (p, e) -> IdxP (transform_path m_env subst p, transform_exp m_env subst e)
    | SliceP (p, e1, e2) -> SliceP (transform_path m_env subst p, transform_exp m_env subst e1, transform_exp m_env subst e2)
    | DotP (p, a) -> DotP (transform_path m_env subst p, a)
  ) $$ path.at % (transform_type m_env subst path.note)

and transform_type (m_env : monoenv) (subst: subst) (typ : typ): typ = 
  (match typ.it with
    | VarT (id, []) when not (Il.Env.mem_typ m_env.il_env id) -> 
      (* It is a type parameter, subst it *)
      (Il.Subst.subst_typ subst typ).it
    | VarT (id, args) when args <> [] ->
      let subst_args = List.map (transform_arg m_env subst) args in 
      let (type_args, normal_args) = List.partition is_type_arg subst_args in
      if type_args <> [] 
        then (
          let reduced_args = List.map (fun arg -> reduce_arg m_env.il_env arg) type_args in 
          concrete_dep_types_bind m_env id.it (VarT(id, reduced_args) $ typ.at);
          VarT (transform_id_from_args id reduced_args, normal_args) 
        )
        else (VarT (id, subst_args))
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (e, transform_type m_env subst t)) exp_typ_pairs)
    | IterT (t, iter) -> IterT (transform_type m_env subst t, transform_iter m_env subst iter)
    | t -> t
  ) $ typ.at

and transform_arg (m_env : monoenv) (subst : subst) (arg : arg) : arg =
  (match arg.it with
    | ExpA exp -> ExpA (transform_exp m_env subst exp)
    | TypA typ -> TypA (transform_type m_env subst typ)
    | _ -> arg.it) $ arg.at
  
and transform_param (m_env : monoenv) (subst : subst) (param : param) : param =
  (match param.it with 
    | ExpP (id, typ) -> ExpP (id, transform_type m_env subst typ)
    | p -> p
  ) $ param.at

and transform_bind (m_env : monoenv) (subst : subst) (bind : bind) : bind =
  (match bind.it with
    | ExpB (id, typ) -> ExpB(id, transform_type m_env subst typ)
    | b -> b) $ bind.at
    
and transform_prem (m_env : monoenv) (subst : subst) (prem : prem): prem = 
  (match prem.it with
    | IfPr e -> IfPr (transform_exp m_env subst e)
    | RulePr (id, m, e) -> RulePr (id, m, transform_exp m_env subst e)
    | IterPr (p, iterexp) -> IterPr (transform_prem m_env subst p, transform_iterexp m_env subst iterexp)
    | ElsePr -> ElsePr
    | LetPr (exp1, exp2, ids) -> LetPr (transform_exp m_env subst exp1, transform_exp m_env subst exp2, ids)
  ) $ prem.at

and subst_deftyp (m_env : monoenv) (subst : subst) (deftyp : deftyp): deftyp = 
  (match deftyp.it with
    | AliasT typ -> AliasT (transform_type m_env subst typ)
    | StructT typfields -> StructT (List.map (fun (a, (bs, t, prems), hints) -> 
      (a, (bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typfields)
    | VariantT typcases -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> 
      (m, (bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typcases)
  ) $ deftyp.at

(* TODO think about how to resolve type params for type families*)
and transform_family_type_instances (_m_env : monoenv) (params : param list) (id : id) (insts : inst list): def' list =
  let (type_params, normal_params) = List.partition is_type_param params in
  if not (type_params <> [] && normal_params = []) then [] else
  [TypD (id, params, insts)]

let transform_type_creation (m_env : monoenv) (id : id) (inst : inst) : def' list =
  match inst.it with 
    | InstD (_, args, deftyp) -> 
      let transform_deftyp func = match args, StringMap.find_opt id.it m_env.concrete_dependent_types with
        | [], None -> (* Means its a normal type *) 
          [TypD (id, [], [InstD ([], [], func Il.Subst.empty) $ inst.at])]
        | _, None -> 
          print_endline ("WARNING: dependent type " ^ id.it ^ " is not being used, removing it.");
          [] (* Remove the dependent type as not used *)
        | _, Some set_ref ->
          List.iter ( fun t -> 
            let dep_args = get_dependent_type_args t in 
            let type_args = List.filter is_type_arg args in
            let subst = Option.value (try Il.Eval.match_list match_arg m_env.il_env Il.Subst.empty dep_args type_args with Irred -> None) ~default:Il.Subst.empty in
            let def' = TypD (transform_id_from_args id dep_args, [], [InstD ([], [], func subst) $ inst.at]) in
            add_to_mono_list m_env (def' $ inst.at)
          ) (TypSet.elements !set_ref);
          []
      in
      (match deftyp.it with 
      | AliasT typ -> transform_deftyp (fun subst -> AliasT (transform_type m_env subst typ) $ deftyp.at) 
      | StructT typfields -> (
        transform_deftyp (fun subst -> StructT (List.map (fun (a, (bs, t, prems), hints) -> 
            (a, (List.map (transform_bind m_env subst) bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typfields) 
          $ deftyp.at)
      )
      | VariantT typcases -> 
        transform_deftyp (fun subst -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> 
          (m, (List.map (transform_bind m_env subst) bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typcases) 
        $ deftyp.at)
    )

let transform_clause (m_env : monoenv) (subst : subst) (clause : clause) : clause =
  match clause.it with
    | DefD (binds, args, exp, prems) ->
      DefD (List.map (transform_bind m_env subst) binds, 
      List.map (transform_arg m_env subst) args, 
      transform_exp m_env subst exp, 
      List.map (transform_prem m_env subst) prems) $ clause.at
        
let transform_function_definitions (m_env : monoenv) (id : id) (params: param list) (return_type : typ) (clauses : clause list) (at : Util.Source.region) (is_recursive: bool): def' list =
  let used, unused = List.partition is_type_param params  in
  let apply_recursive def' = match is_recursive with 
    | true -> RecD [def' $ at]
    | false -> def' 
  in
  match (StringMap.find_opt id.it m_env.calls), used with
    | _, [] -> (* function has no type parameters *) 
      let subst = Il.Subst.empty in
      [apply_recursive (DecD (id, params, transform_type m_env subst return_type, List.map (transform_clause m_env subst) clauses))]
    | None, _ -> (* function is not used *) 
      print_endline ("WARNING: function " ^ id.it ^ " is not being used, removing it.");
      []
    | Some set_ref, _ -> (* function has type params *)
      List.iter (fun e -> 
        let (new_id, used_call_args) = get_function_call e in 
        let used_param_ids = List.map get_variable_id_from_param used in 
        let subst = create_args_pairings used_param_ids used_call_args in
        let def' = DecD (new_id.it $ id.at, List.map (transform_param m_env subst) unused, 
          transform_type m_env subst return_type, 
          List.map (transform_clause m_env subst) clauses) in 
        add_to_mono_list m_env ((apply_recursive def') $ at)
      ) (ExpSet.elements !set_ref);
      []

let transform_rule (m_env : monoenv) (rule : rule) : rule =
  match rule.it with
    | RuleD (rule_id, binds, mixop, exp, prems) ->
      RuleD(rule_id, 
      List.map (transform_bind m_env Subst.empty) binds, 
      mixop, 
      transform_exp m_env Subst.empty exp, 
      List.map (transform_prem m_env Subst.empty) prems) $ rule.at

let rec transform_def (m_env : monoenv) (def : def) : def list =
  (match def.it with
    | TypD (id, _, [inst]) when Mono_nat_subset.check_normal_type_creation inst -> transform_type_creation m_env id inst
    | TypD (id, params, insts) -> transform_family_type_instances m_env params id insts
    | RelD (id, mixop, typ, rules) -> 
      [RelD (id, mixop, typ, List.map (transform_rule m_env) rules)]
    | RecD [{it = DecD (id, params, typ, clauses); _}] -> transform_function_definitions m_env id params typ clauses def.at true
    | DecD (id, params, typ, clauses) -> transform_function_definitions m_env id params typ clauses def.at false
    | RecD defs -> let new_defs = List.concat_map (transform_def m_env) defs in
      (match new_defs with
        | [] -> []
        | _ -> [RecD new_defs]
      )
    | _ -> [def.it]
  ) |> List.map (fun new_def -> new_def $ def.at) 

let reorder_monomorphized_functions (m_env : monoenv) (def : def): def list =
  let rec get_ids d = (match d.it with
      | TypD (id, _, _) | RelD (id, _, _, _) | DecD (id, _, _, _) -> [id.it]
      | RecD defs -> List.concat_map get_ids defs
      | _ -> []
    ) in
  
  let partition_list mono_list def = 
    let free_def_vars = Free.free_def def in
    List.partition (fun d -> 
      let ids = Free.Set.of_list (get_ids d) in
      let typs = Free.Set.is_empty (Free.Set.inter ids free_def_vars.typid) in
      let funcs = Free.Set.is_empty (Free.Set.inter ids free_def_vars.defid) in
      typs && funcs
    ) mono_list in

  let (rest, filtered_mono_list) = partition_list m_env.mono_list def in
  m_env.mono_list <- rest;
  filtered_mono_list @ [def]

let rec repeat_reordering (m_env : monoenv) (defs : def list) : def list =
  match (m_env.mono_list) with
    | [] -> defs
    | _ -> repeat_reordering m_env (List.concat_map (reorder_monomorphized_functions m_env) defs)

(* Main transformation function *)
let transform (script: Il.Ast.script) =
  let m_env = new_env in 
  m_env.il_env <- Il.Env.env_of_script script;
  (* Reverse the script in order to monomorphize nested ones correctly *)
  let transformed_script = List.rev (List.concat_map (transform_def m_env) (List.rev script)) in
  print_env m_env;
  repeat_reordering m_env transformed_script