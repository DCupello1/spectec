


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
open Xl


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
}

let new_env() = 
{
    calls = StringMap.empty;
    concrete_dependent_types = StringMap.empty;
    il_env = Il.Env.empty;
}

let mono = "Monomorphization"

let empty_tuple_exp at = TupE [] $$ at % (TupT [] $ at)

let _map_fst f = List.map (fun (v1, v2) -> (f v1, v2))

let map_snd f = List.map (fun (v1, v2) -> (v1, f v2))

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

let rec check_dependent_types_func_decl (arglist : arg list) (return_type : typ) : int list = 
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
    | TupE [] -> ""
    | TupE exps -> "t" ^ String.concat "_" (List.map to_string_exp exps) 
    | CaseE (mixop, {it = TupE []; _}) -> to_string_mixop mixop 
    | CaseE (mixop, exp) -> to_string_mixop mixop ^ "_" ^ to_string_exp exp
    | CvtE (e, _, _) -> to_string_exp e
    | SubE (e, _, _) -> to_string_exp e
    | _ -> error exp.at mono "Cannot transform these into strings"

and to_string_typ (typ : typ) : string = 
  match typ.it with
    | BoolT | NumT _ | TextT -> string_of_typ typ
    | VarT (id, args) -> id.it ^ "_" ^ String.concat "__" (List.map to_string_arg args)
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
  id.it ^ "_mono_" ^ String.concat "__" (List.map to_string_arg args) $ id.at

and transform_string_from_exps (text : string) (exps : exp list): string =
  if exps = [] then text else 
  text ^ "_mono_" ^ String.concat "__" (List.map to_string_exp exps)
and transform_id_from_exps (id : id) (exps : exp list): id =
  transform_string_from_exps id.it exps $ id.at

(* TODO fix this to remove the correct holes in the more complicated case *)
and transform_mixop_from_exps (m : mixop) (num_kept : int) (exps : exp list): mixop =
  if exps = [] then m else
  match m with
    | [{it = Atom.Atom a; _} as atom]::tail when List.for_all ((=) []) tail -> 
      [Atom.Atom (transform_string_from_exps a exps) $$ atom.at % atom.note]::(List.init num_kept (fun _ -> []))
    | _ -> 
      let rec aux num_empty = function
        | [] -> []
        | [] :: ls when num_empty > num_kept -> aux (num_empty + 1) ls
        | [] :: ls -> [] :: aux (num_empty + 1) ls
        | _ :: ls -> aux num_empty ls
      in
      List.mapi (fun i atoms -> 
      let length_last = List.length m in 
      let new_atom = Atom.Atom (transform_string_from_exps "" exps) $$ (no_region, Atom.info "") in
      if i = length_last - 1 then atoms @ [new_atom] else atoms) (aux 0 m)

let create_args_pairings (args_ids : id list) (concrete_args : arg list): subst =
  List.fold_left (fun acc (id, arg) -> match arg.it with
    | ExpA exp -> Il.Subst.add_varid acc id exp
    | TypA typ -> Il.Subst.add_typid acc id typ
    | DefA x -> Il.Subst.add_defid acc id x
    | GramA g -> Il.Subst.add_gramid acc id g) Il.Subst.empty (List.combine args_ids concrete_args)

(* Terminal cases traversal *)

let rec check_reducible_exp (exp : exp) : bool =
  match exp.it with
    | BoolE _ | NumE _ | TextE _ -> true
    | UnE (_, _, e) -> check_reducible_exp e
    | BinE (_, _, e1, e2) -> check_reducible_exp e1 && check_reducible_exp e2
    | CmpE (_, _, e1, e2) -> check_reducible_exp e1 && check_reducible_exp e2
    | TupE exps -> List.for_all check_reducible_exp exps 
    | CvtE (e, _, _) -> check_reducible_exp e
    | SubE (e, _, _) -> check_reducible_exp e
    | ListE exps -> List.for_all check_reducible_exp exps 
    | CaseE (_, e) -> check_reducible_exp e
    | _ -> false

and check_reducible_typ (typ: typ): bool =
  match typ.it with
    | IterT (t, _iter) -> check_reducible_typ t
    | VarT (_, args) -> check_reducible_args args
    | TupT exp_typ_pairs -> List.map snd exp_typ_pairs |> List.for_all check_reducible_typ
    | _ -> true

and check_reducible_arg (arg: arg): bool =
  match arg.it with
    | TypA typ -> check_reducible_typ typ
    | ExpA exp -> check_reducible_exp exp
    | _ -> false

and check_reducible_args (args: arg list): bool =
  List.for_all check_reducible_arg args

(* Monomorphization Pass *)

let get_dependent_type_args (typ : typ): arg list = 
  match typ.it with  
    | VarT (_, concrete_args) -> concrete_args
    | _ -> error typ.at mono "Applied monomorphization on a non-concrete dependent type"

let get_variable_id_from_arg (arg : arg): id = 
  match arg.it with
    | ExpA ({it = VarE id; _}) -> id
    | ExpA ({it = SubE ({it = VarE id;_}, _, _); _}) -> id
    | TypA ({it = VarT (id, _); _}) -> id
    | _ -> error arg.at mono "Arguments on LHS have something other than id"

let get_tuple_from_type (typ : typ): ((exp * typ) list) option =
  match typ.it with
    | TupT (e_t) -> Some e_t
    | _ -> None (* We don't need to worry about the case of it being single typed *)
  
let rec get_all_variable_ids_arg (arg : arg): string list = 
  match arg.it with
    | ExpA exp -> get_all_variable_ids_exp exp
    | TypA typ -> get_all_variable_ids_typ typ
    | _ -> []

and get_all_variable_ids_exp (exp : exp): string list = 
  match exp.it with
    | VarE id -> [id.it]
    | CaseE (_, e) -> get_all_variable_ids_exp e
    | CallE (_, args) -> List.concat_map get_all_variable_ids_arg args
    | SubE (e, _, _) -> get_all_variable_ids_exp e
    | _ -> []

and get_all_variable_ids_typ (typ : typ): string list =
  match typ.it with
    | VarT (id, args) -> id.it :: List.concat_map get_all_variable_ids_arg args
    | IterT (t, _) -> get_all_variable_ids_typ t
    | TupT exp_typ_pairs -> List.concat_map (fun (_, t) -> get_all_variable_ids_typ t) exp_typ_pairs
    | _ -> []

and get_all_variable_ids_bind (bind : bind): string list =
  match bind.it with
    | ExpB (id, typ) -> id.it :: get_all_variable_ids_typ typ
    | _ -> []


let rec check_dep_type t = match t.it with
  | VarT (_ , []) -> false
  | VarT (_, _) -> true
  | IterT (t, _) -> check_dep_type t
  | TupT exp_typ_pairs -> List.map snd exp_typ_pairs |> List.exists check_dep_type
  | _ -> false

and check_dep_typ_in_bind b = 
  match b.it with
    | ExpB (_, typ) -> check_dep_type typ
    | _ -> false

let rec check_used_dependent_types_case_args (exp_typ_pairs : (exp * typ) list): (exp * typ) list * (exp * typ) list =
  match exp_typ_pairs with
    | [] -> ([], [])
    | (_, t) as p :: ps -> 
      let id_t = match t.it with
        | VarT (id, _) -> id.it
        | _ -> ""
      in 
      let (used_dep, unused) = check_used_dependent_types_case_args ps in
      if List.mem id_t (List.concat_map (fun (_, t) -> get_all_variable_ids_typ t) (List.filter (fun (_, t) -> check_dep_type t) ps))
        then (p :: used_dep, unused)
        else (used_dep, p :: unused)

let rec check_used_dependent_types_relation_binds (exp_typ_pairs : bind list): bind list * bind list =
  match exp_typ_pairs with
    | [] -> ([], [])
    | {it = ExpB (id, _); _} as b :: bs -> 
      let (used_dep, unused) = check_used_dependent_types_relation_binds bs in
      if List.mem id.it (List.concat_map get_all_variable_ids_bind (List.filter check_dep_typ_in_bind bs))
        then (b :: used_dep, unused)
        else (used_dep, b :: unused)
    | b :: bs -> 
      let (used_dep, unused) = check_used_dependent_types_relation_binds bs in
      (used_dep, b :: unused)
      
(* let rec check_used_dependent_types_params (params : param list) (return_type : typ) = 
  match params with
    | [] -> ([], [])
    | p :: ps -> 
      let id_p = match p.it with
        | ExpP (id, _) -> id.it
        | TypP id -> id.it
        | _ -> ""
      in
      let (used_dep, unused) = check_used_dependent_types_params ps in
      if List.mem  *)

let rec transform_exp (m_env : monoenv) (subst : subst) (exp : exp): exp =
  let t_func = transform_exp m_env subst in
  (match exp.it with
    | UnE (unop, optyp, e) -> UnE (unop, optyp, t_func e)
    | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2)
    | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2)
    | TupE exps -> TupE (List.map t_func exps)
    | ProjE (e, i) -> ProjE (t_func e, i)
    | CaseE (m, e) -> CaseE (m, t_func e) (* TODO think about handling new inductive cases *)
    | UncaseE (e, m) -> UncaseE (t_func e, m)
    | OptE (Some e) -> OptE (Some (t_func e))
    | TheE e -> TheE (t_func e)
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
    | CallE (id, args) -> CallE (id, args) (* TODO propogate well *)
    | IterE (e, iterexp) -> IterE (t_func e, transform_iterexp m_env subst iterexp)
    | CvtE (e, ntyp1, ntyp2) -> CvtE (t_func e, ntyp1, ntyp2)
    | SubE (e, t1, t2) -> SubE (t_func e, transform_dependent_type m_env subst t1, transform_dependent_type m_env subst t2)
    | e -> e
  ) $$ exp.at % (transform_dependent_type m_env subst exp.note)

and transform_iterexp (m_env : monoenv) (subst : subst) (iterexp : iterexp): iterexp = 
  let (iter, id_exp_pairs) = iterexp in
  (iter, map_snd (transform_exp m_env subst) id_exp_pairs)

and transform_path (m_env : monoenv) (subst : subst) (path : path): path = 
  (match path.it with
    | RootP -> RootP
    | IdxP (p, e) -> IdxP (transform_path m_env subst p, transform_exp m_env subst e)
    | SliceP (p, e1, e2) -> SliceP (transform_path m_env subst p, transform_exp m_env subst e1, transform_exp m_env subst e2)
    | DotP (p, a) -> DotP (transform_path m_env subst p, a)
  ) $$ path.at % (transform_dependent_type m_env subst path.note)

and transform_dependent_type (m_env : monoenv) (subst: subst) (typ : typ): typ = 
  let reduced_typ = Il.Eval.reduce_typ m_env.il_env (Il.Subst.subst_typ subst typ) in
  (match reduced_typ.it with
    | VarT (id, args) when args <> [] -> 
      if check_reducible_args args 
        then (
          concrete_dep_types_bind m_env id.it (VarT(id, args) $ typ.at); 
          VarT (transform_id_from_args id args, []) 
        )
        else typ.it
          (* else error typ.at mono "Cannot monomorphize correctly" *)
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (e, transform_dependent_type m_env subst t)) exp_typ_pairs)
    | IterT (t, iter) -> IterT (transform_dependent_type m_env subst t, iter)
    | t -> t
  ) $ typ.at

let transform_bind (m_env : monoenv) (subst : subst) (bind : bind) : bind =
  (match bind.it with
    | ExpB (id, typ) -> ExpB(id, transform_dependent_type m_env subst typ)
    | b -> b) $ bind.at
    
let rec subst_and_reduce_prems (m_env : monoenv) (subst : subst) (prem : prem): prem = 
  match prem.it with
    | IfPr exp -> IfPr (Il.Eval.reduce_exp m_env.il_env (Il.Subst.subst_exp subst exp)) $ prem.at
    | IterPr (p, _) -> subst_and_reduce_prems m_env subst p
    | _ -> Il.Subst.subst_prem subst prem

let subst_and_reduce_deftyp (m_env : monoenv) (subst : subst) (deftyp : deftyp): deftyp = 
  let new_deftyp = Il.Subst.subst_deftyp subst deftyp in
  (match new_deftyp.it with
    | AliasT typ -> AliasT (transform_dependent_type m_env subst typ)
    | StructT typfields -> StructT (List.map (fun (a, (bs, t, prems), hints) -> 
      (a, (bs, transform_dependent_type m_env subst t, List.map (subst_and_reduce_prems m_env subst) prems), hints) ) typfields)
    | VariantT typcases -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> 
      (m, (bs, transform_dependent_type m_env subst t, List.map (subst_and_reduce_prems m_env subst) prems), hints) ) typcases)
  ) $ deftyp.at
    

(* For now this deals with simple type cases that can be trivially substituted *)
let get_cases_instances (inst : inst): typcase list =
  match inst.it with
    | InstD (_, _, deftyp) -> match deftyp.it with
      | AliasT _typ -> []
      | StructT _typfields -> []
      | VariantT typcases -> if List.for_all (fun (_, (_, t, _), _) -> t.it = TupT []) typcases
        then typcases
        else []

let product_of_lists (lists : 'a list list) = 
  List.fold_left (fun acc seq ->
    Seq.flat_map (fun existing -> 
      Seq.map (fun v -> v :: existing) seq) acc) (Seq.return []) (List.map List.to_seq lists) 

let transform_type_case (m_env : monoenv) (subst : subst) (typc : typcase) : typcase list = 
  let (m, (bs, t, prems), hints) = typc in
  match get_tuple_from_type t with
    | None -> [(m, (List.map (transform_bind m_env subst) bs, transform_dependent_type m_env subst t, List.map (subst_and_reduce_prems m_env subst) prems), hints)]
    | Some exp_typ_pairs -> 
      let used, unused = check_used_dependent_types_case_args exp_typ_pairs in

      let used_ids = List.filter_map (fun (_, t) -> match t.it with
        | VarT (id, _) -> Option.map (fun (_, insts) -> match insts with 
          | [inst] -> List.map (fun typc -> let (m, (_, typ, _), _) = typc in 
           (id, (CaseE (m, empty_tuple_exp typ.at)) $$ (typ.at, typ))) (get_cases_instances inst)
          | _ -> [] (* It shouldn't be a family type *)) (Il.Env.find_opt_typ m_env.il_env id)
        | _ -> None) used in
      let cases_seq = product_of_lists used_ids in
      let subst_seq = Seq.map (List.fold_left (fun acc (id, exp) -> Il.Subst.add_varid acc id exp) subst) cases_seq in
      Seq.map (fun new_subst -> 
        let new_typ = TupT (List.map (fun (e, typ) -> (e, (transform_dependent_type m_env new_subst typ))) unused) $ t.at in
        let new_binds = List.map (transform_bind m_env new_subst) (List.filter (fun b -> match b.it with
          | ExpB (id, _) -> not (Il.Subst.mem_varid new_subst id)
          | _ -> false) 
        bs) in
        let new_prems = List.map (subst_and_reduce_prems m_env new_subst) prems in
        let new_mixop = transform_mixop_from_exps m (List.length unused) (List.map snd (Il.Subst.bindings_varid new_subst)) in
        (new_mixop, (new_binds, new_typ, new_prems), hints)
      ) subst_seq |> List.of_seq

let transform_type_creation (m_env : monoenv) (id : id) (inst : inst) : def' list =
  match inst.it with 
    | InstD (binds, args, deftyp) -> (match deftyp.it with 
      | AliasT typ -> (match args, StringMap.find_opt id.it m_env.concrete_dependent_types with
        | [], None -> (* Means its a normal type *) 
            let new_deftyp = AliasT (transform_dependent_type m_env Il.Subst.empty typ) $ deftyp.at in 
            [(TypD (id, [], [InstD (binds, [], new_deftyp) $ inst.at]))]
        | _, None -> [] (* Remove the dependent type as not used *)
        | _, Some set_ref -> 
          List.map ( fun t -> 
            let dep_args = get_dependent_type_args t in 
            let args_ids = List.map get_variable_id_from_arg args in  
            let subst = create_args_pairings args_ids dep_args in
            let new_deftyp = AliasT (transform_dependent_type m_env subst typ) $ deftyp.at in 
            TypD (transform_id_from_args id dep_args, [], [InstD ([], [], new_deftyp) $ inst.at])
            ) (TypSet.elements !set_ref)  
      )
      | StructT typfields -> (
        let new_deftyp = StructT (List.map (fun (a, (bs, t, prems), hints) -> (a, (bs, transform_dependent_type m_env Il.Subst.empty t, prems), hints)) typfields) $ deftyp.at in
        [TypD (id, [], [InstD ([], [], new_deftyp) $ inst.at])] (* Ignore args for now, there shouldn't be any here *)
      )
      | VariantT typcases -> (match args, StringMap.find_opt id.it m_env.concrete_dependent_types with
        | [], None -> (* Means its a normal type *) 
          let new_deftyp = VariantT (List.concat_map (transform_type_case m_env Il.Subst.empty) typcases) $ deftyp.at in
          [TypD (id, [], [InstD ([], [], new_deftyp) $ inst.at])]
        | _, None -> [] (* Remove the dependent type as not used *)
        | _, Some set_ref ->
          List.map ( fun t -> 
            let dep_args = get_dependent_type_args t in 
            let args_ids = List.map get_variable_id_from_arg args in  
            let subst = create_args_pairings args_ids dep_args in
            let new_deftyp = VariantT (List.concat_map (transform_type_case m_env subst) typcases) $ deftyp.at in 
              TypD (transform_id_from_args id dep_args, [], [InstD ([], [], new_deftyp) $ inst.at])
            ) (TypSet.elements !set_ref)
      )
    )

let get_concrete_matches (m_env : monoenv) (bind : bind) : (id * exp) list = 
  match bind.it with
    | ExpB (var_id, {it = VarT (typ_id, _); _}) -> (match (Il.Env.find_opt_typ m_env.il_env typ_id) with
      | Some (_params, [inst]) -> 
        List.map (fun (m, (_, t, _), _) -> (var_id, CaseE (m, empty_tuple_exp t.at) $$ t.at % t)) (get_cases_instances inst)
      | _ -> []
    )
    | _ -> []


(* TODO make this work on arguments as well *)
let transform_family_type_instances (m_env : monoenv) (id : id) (inst : inst): def' list = 
  match inst.it with 
    | InstD (binds, _, deftyp) -> 
      let cases_seq = product_of_lists (List.map (get_concrete_matches m_env) binds) in
      let subst_seq = Seq.map (List.fold_left (fun acc (id, exp) -> Il.Subst.add_varid acc id exp) Il.Subst.empty) cases_seq in
      Seq.map (fun subst ->
        let new_id = transform_id_from_exps id (List.map snd (Il.Subst.bindings_varid subst)) in
        let new_inst = InstD ([], [], subst_and_reduce_deftyp m_env subst deftyp) $ inst.at in 
        TypD (new_id, [], [new_inst]) 
      ) subst_seq |> List.of_seq

(* let transform_function_definitions (m_env : monoenv) (id : id) (params: param list) (return_type : typ) (clauses : clause list): def' list =
  match (StringMap.find_opt id.it m_env.concrete_dependent_types) with *)

let transform_rule (m_env : monoenv) (rule : rule) : rule list =
  match rule.it with
    | RuleD (rule_id, binds, mixop, exp, prems) ->
      let (used_deps, unused) = check_used_dependent_types_relation_binds binds in
      let cases_seq = product_of_lists (List.map (get_concrete_matches m_env) used_deps) in
      let subst_seq = Seq.map (List.fold_left (fun acc (id, exp) -> Il.Subst.add_varid acc id exp) Il.Subst.empty) cases_seq in
      Seq.map (fun subst ->
        let new_id = transform_id_from_exps rule_id (List.map snd (Il.Subst.bindings_varid subst)) in
        let new_prems = List.map (subst_and_reduce_prems m_env subst) prems in
        let subst_exp = Il.Subst.subst_exp subst exp in 
        RuleD (new_id, List.map (transform_bind m_env subst) unused, mixop, transform_exp m_env subst subst_exp, new_prems) $ rule.at
      ) subst_seq |> List.of_seq

(* Hack for now until there is a way to distinguish family types well *)
let check_normal_type_creation (inst : inst) : bool = 
  match inst.it with
    | InstD (_, args, _) -> List.for_all (fun arg -> 
      match arg.it with 
        | ExpA {it = VarE _; _} -> true
        | _ -> false  
    ) args 

let rec transform_def (m_env : monoenv) (def : def) : def list =
  (match def.it with
    | TypD (id, _, [inst]) when check_normal_type_creation inst -> transform_type_creation m_env id inst
    | TypD (id, _params, insts) -> List.concat_map (transform_family_type_instances m_env id) insts
    | RelD (id, mixop, typ, rules) -> [RelD (id, mixop, typ, List.concat_map (transform_rule m_env) rules)]

    | DecD (_id, _params, _typ, _clauses) -> [def.it](*transform_function_definitions id params typ clauses*)
    | RecD defs -> [RecD (List.concat_map (transform_def m_env) defs)]
    | _ -> [def.it]) |> List.map (fun new_def -> new_def $ def.at) 

(* Main transformation function *)
let transform (script: Il.Ast.script) =
  let m_env = new_env() in 
  m_env.il_env <- Il.Env.env_of_script script;
  (* Reverse the script in order to monomorphize nested ones correctly *)
  let transformed_script = List.rev (List.concat_map (transform_def m_env) (List.rev script)) in
  print_env m_env;
  transformed_script

