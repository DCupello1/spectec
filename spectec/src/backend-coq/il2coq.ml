open Il.Ast
open Il.Print
open Coqast
open Util
open Source
open Case
open Either

(* Util functions for transform *)
module IdSet = Set.Make(String)
let reserved_ids = ["N"; "in"; "In"; "()"; "tt"; "Import"; "Export"; "List"; "String"; "Type"; "list"; "nat"] |> IdSet.of_list
let error at msg = Error.error at "Coq Generation" msg
let family_type_suffix = "entry"
let coerce_prefix = "coec_"
let var_prefix = "v_"
let func_prefix = "fun_"

let rec list_split (f : 'a -> bool) (l : 'a list) = match l with
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

let rec partition_eitherlist (xs : ('a, 'b) Either.t list) = 
  match xs with
    | [] -> ([], [])
    | (Left x) :: xs' -> let (lefts, rights) = partition_eitherlist xs' in
      (x :: lefts, rights)
    | Right x :: xs' -> let (lefts, rights) = partition_eitherlist xs' in
      (lefts, x :: rights)

(* Temporary workaround for fixing family matching (Only works for family types of one dependent type param) *)
let family_helper = Hashtbl.create 30

(* Case functions that handles case expressions and record appending*)
let env_ref = ref (Case.new_env())

let rec get_actual_case_name (env : env) (id : id) =
  let (n_id, num_args, struct_type) = find "Case" env.vars id in
  (match struct_type with 
    | TypeAlias -> let actual_id, final_args = get_actual_case_name env n_id in
    (actual_id, num_args + final_args)
    | Inductive -> (n_id, num_args)
    | _ -> error id.at "Should be a Variant type or type alias"
  )

let gen_case_name (env : env) (t : typ) =
  match t.it with
    | VarT (id, _) -> get_actual_case_name env id
    | _ -> error t.at "Should not happen"

let rec get_struct_type (env : env) (id : id) =
  let (n_id, _, struct_type) = find "Case" env.vars id in
  (match struct_type with 
    | TypeAlias -> get_struct_type env n_id
    | Inductive -> Inductive
    | Record -> Record
    | Terminal -> Terminal
  )

(* Id transformation *)
let transform_id' (s : text) = match s with
  | s when IdSet.mem s reserved_ids -> "reserved__" ^ s
  | s -> String.trim (String.map (function
     | '.' -> '_'
     | '-' -> '_'
     | '*' -> ' '
     | '?' -> ' '
     | '^' -> ' '
     | c -> c
     ) s)

let transform_id (id : id) = transform_id' id.it

let transform_var_id (id : id) = var_prefix ^ transform_id' id.it

let transform_fun_id (id : id) = func_prefix ^ transform_id' id.it 

(* Identifier generation *)
let gen_typ_name (t : typ) =
  match t.it with
    | VarT (id, _) -> id.it
    | _ -> "" (* Not an issue if this happens *)
  
let get_typ_args (t : typ) = 
  match t.it with
    | VarT (_, args) -> args
    | _ -> []

let gen_exp_name (e : exp) =
  match e.it with
    | VarE id -> id.it
    | _ -> "_" 

let get_typ_name (t : typ) = 
  match t.it with
    | VarT (id, _) -> Some id
    | _ -> None
let gen_bind_name (bind : bind) =
  match bind.it with
    | ExpB (id, _) -> transform_id id
    | TypB id -> transform_id id
    | DefB (id, _, _) -> transform_id id
    | GramB (id, _, _) -> transform_id id 
    
let gen_arg_names (arg : arg) = 
  match arg.it with
    | ExpA e -> let rec gen_argexp_name exp = 
      (match exp.it with
        | VarE _ -> [gen_typ_name exp.note]
        | CaseE (_, exp') -> gen_typ_name exp.note :: gen_argexp_name exp'
        | TupE tups -> List.concat_map gen_argexp_name tups
        | _ -> []
      ) in 
      gen_argexp_name e
    | TypA _ -> []
    | _ -> []
      
(* Family types infer function *)
let infer_match_name (args : arg list) (type_name : text) =
  let rec infer_function lst =
    match lst with
      | [] -> None
      | l :: lst' -> let name = (type_name ^ "__" ^ l) in 
      if (Hashtbl.mem family_helper name) then Some name else infer_function lst'
    in
  let rec infer_match_name_from_args ags = 
    match ags with
      | [] -> None
      | a :: ags' -> let name_list = gen_arg_names a in 
        let inferred_name = infer_function name_list in
        if Option.is_none inferred_name 
          then infer_match_name_from_args ags' 
          else inferred_name
  in
  infer_match_name_from_args args 

let find_typ (args : arg list) (type_name : text) =
  let rec infer_function lst =
    match lst with
      | [] -> None
      | l :: lst' -> let name = (type_name ^ "__" ^ l) in 
      match (Hashtbl.find_opt family_helper name) with 
        | Some typ -> Some typ 
        | _ -> infer_function lst'
    in
  let rec infer_match_name_from_args ags = 
    match ags with
      | [] -> None
      | a :: ags' -> let name_list = gen_arg_names a in 
        let inferred_name = infer_function name_list in
        if Option.is_none inferred_name 
          then infer_match_name_from_args ags' 
          else inferred_name in
  infer_match_name_from_args args 

(* Atom functions *)
let transform_atom (a : atom) = 
  match a.it with
    | Atom s -> transform_id' s
    | _ -> ""

let is_atomid (a : atom) =
  match a.it with
    | Atom _ -> true
    | _ -> false

let transform_mixop (m : mixop) = match m with
  | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> transform_id' a
  | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )

(* Type functions *)

let is_terminal_type (typ : typ) =
  match typ.it with
    | VarT (_, args) -> args = [] 
    | (BoolT | NumT _ | TextT) -> true
    | _ -> false

let transform_itertyp (it : iter) =
  match it with
    | Opt -> T_type_basic T_opt
    | List | List1 | ListN _ -> T_type_basic T_list

let transform_numtyp (typ : numtyp) = 
  match typ with
    | `NatT -> T_type_basic T_nat
    | `IntT -> T_type_basic T_nat
    | `RatT -> T_type_basic T_nat (*T_unsupported "rat"*)
    | `RealT -> T_type_basic T_nat (*T_unsupported "real"*)

let rec transform_type (typ : typ) =
  match typ.it with
    | VarT (id, []) -> T_ident [transform_id id]
    | VarT (id, args) -> T_app (T_ident [transform_id id], List.map transform_arg args)
    | BoolT -> T_type_basic T_bool
    | NumT nt -> transform_numtyp nt
    | TextT -> T_type_basic T_string 
    | TupT [] -> T_type_basic T_unit
    | TupT typs -> T_tuple (List.map (fun (_, t) -> transform_type t) typs)
    | IterT (typ, iter) -> T_app (transform_itertyp iter, [transform_type typ])

(* Erases the dependent type for inductive families *)
and erase_dependent_type (typ : typ) = 
  match typ.it with
    | IterT (t, iter) -> T_app (transform_itertyp iter, [erase_dependent_type t])
    | TupT [] -> T_type_basic T_unit
    | TupT typs -> T_tuple (List.map (fun (_, t) -> erase_dependent_type t) typs)
    | VarT (id, _) -> let inferred_opt = Hashtbl.mem family_helper (transform_id id) in      
      if inferred_opt then T_ident [transform_id id] else transform_type typ
    | _ -> transform_type typ

and check_family_dependent_type (typ : typ) = 
  match typ.it with
    | IterT (t, _iter) -> check_family_dependent_type t
    | TupT typs -> List.fold_left (fun acc (_, t) -> acc || check_family_dependent_type t) false typs
    | VarT (id, _) -> Hashtbl.mem family_helper (transform_id id)
    | _ -> false

and transform_return_type (typ : typ) =
  match typ.it with
    (* Only works for 1-dimensional lists. 
    (Which is fine since type coercing for higher dimensional lists is too much anyways)*)
    | IterT ({it = VarT (id, args); _}, _) -> 
      let inferred_opt = Hashtbl.mem family_helper (transform_id id) in      
      if inferred_opt 
      then T_ident ["list"; transform_id id] 
      else T_app (T_ident ["list"; transform_id id], List.map transform_arg args)
    | IterT (typ, iter) -> T_app (transform_itertyp iter, [transform_return_type typ])
    | _ -> erase_dependent_type typ

and transform_typ_args (typ : typ) =
  match typ.it with
    | TupT [] -> []
    | TupT typs -> List.map (fun (e, t) -> (var_prefix ^ gen_exp_name e, erase_dependent_type t)) typs
    | _ -> [("_", erase_dependent_type typ)]

and remove_iter_typ (typ : typ) = 
  match typ.it with
    | IterT (typ, _) -> typ
    | _ -> typ

and transform_tuple_to_relation_args (t : typ) =
  match t.it with
    | TupT typs -> List.map (fun (_, t) -> erase_dependent_type t) typs
    | _ -> [erase_dependent_type t]

(* Expression functions *)
and transform_exp (exp : exp) =
  match exp.it with 
    | VarE id -> if (Hashtbl.mem family_helper (gen_typ_name exp.note)) then T_cast (T_ident [transform_var_id id], erase_dependent_type exp.note) else T_ident [transform_var_id id]
    | BoolE b -> T_exp_basic (T_bool b)
    | NumE (`Nat n) -> T_exp_basic (T_nat n)
    | NumE _ -> T_unsupported (string_of_exp exp)
    | TextE txt -> T_exp_basic (T_string txt)
    | UnE (unop, _, exp) -> transform_unop unop exp
    | BinE (binop, _, exp1, exp2) -> T_app_infix (transform_binop binop, transform_exp exp1, transform_exp exp2)
    | CmpE (cmpop, _, exp1, exp2) -> T_app_infix (transform_cmpop cmpop, transform_exp exp1, transform_exp exp2)
    | TupE [] -> T_exp_basic T_exp_unit
    | TupE exps -> T_match (List.map transform_exp exps) 
    | ProjE (e, n) -> T_app (T_exp_basic T_listlookup, [transform_exp e; T_exp_basic (T_nat (Z.of_int n))])
    | CaseE (mixop, e) -> let actual_id, num_args = gen_case_name !env_ref exp.note in 
      T_app (T_ident [transform_id actual_id; transform_mixop mixop], List.append (List.init num_args (fun _ -> T_ident ["_ "])) (transform_tuple_exp transform_exp e))
    | UncaseE (e, _mixop) -> transform_exp e (* TODO check if this is fine *)
    | OptE (Some e) -> T_app (T_exp_basic T_some, [transform_exp e])
    | OptE None -> T_exp_basic T_none
    | TheE e -> T_app (T_exp_basic T_the, [transform_exp e])
    | StrE expfields -> T_record_fields (List.map (fun (a, e) -> (gen_typ_name exp.note ^ "__" ^ transform_atom a, transform_exp e)) expfields)
    | DotE (e, atom) -> T_app (T_ident [gen_typ_name e.note; transform_atom atom], [transform_exp e])
    | CompE (exp1, exp2) -> T_app_infix (T_exp_basic T_concat, transform_exp exp1, transform_exp exp2)
    | ListE exps -> T_list (List.map transform_exp exps)
    | LenE e -> T_app (T_exp_basic T_listlength, [transform_exp e])
    | CatE (exp1, exp2) -> T_app (T_exp_basic T_listconcat, [T_ident ["_"] ;transform_exp exp1; transform_exp exp2])
    | IdxE (exp1, exp2) -> T_app (T_exp_basic T_listlookup, [transform_exp exp1; transform_exp exp2])
    | SliceE (exp1, exp2, exp3) -> T_app (T_exp_basic T_slicelookup, [transform_exp exp1; transform_exp exp2; transform_exp exp3])
    | UpdE (exp1, path, exp2) -> T_update (transform_path_start path exp1, transform_exp exp1, transform_exp exp2)
    | ExtE (exp1, path, exp2) -> T_extend (transform_path_start path exp1, transform_exp exp1, transform_exp exp2)
    | CallE (id, args) -> T_app (T_ident [transform_fun_id id], List.map transform_arg args)
    | IterE (exp, (iter, ids)) ->  
        let exp1 = transform_exp exp in
        let t_iter = if iter = Opt then I_option else I_list in
        (match iter, ids, exp.it with
        | (List | List1 | ListN _), [], _ -> T_list [exp1] 
        | (List | List1 | ListN _ | Opt), _, (VarE _ | IterE _) -> exp1 
        | (List | List1 | ListN _ | Opt), [(v, _)], (SubE ({it = VarE _; _}, typ1, typ2)) -> T_app (T_ident ["list"; gen_typ_name typ1; gen_typ_name typ2], [T_ident [transform_var_id v]])
        | (List | List1 | ListN _ | Opt), [(v, _)], (SubE (e, typ1, typ2)) -> T_app (T_ident ["list"; gen_typ_name typ1; gen_typ_name typ2], [T_map (t_iter, transform_var_id v, transform_exp e)])
        | Opt, [(_, _)], OptE (Some e) -> T_app (T_exp_basic T_some, [transform_exp e])
        | (List | List1 | ListN _ | Opt), [(v, _)], _ -> T_map (t_iter, transform_var_id v, exp1)
        | (List | List1 | ListN _ | Opt), [(v, _); (s, _)], _ -> T_zipwith (t_iter, transform_var_id v, transform_var_id s, transform_exp exp)
        | _ -> exp1
      ) 
    | SubE (e, _, typ2) -> T_cast (transform_exp e, transform_type typ2)
    | LiftE e -> transform_exp e (* TODO *)
    | CvtE (e, _t1, _t2) -> transform_exp e (* TODO *)
    | MemE _ -> T_unsupported ("MemE: " ^ string_of_exp exp) (* TODO *)

and transform_match_exp (exp : exp) =
  match exp.it with
  | VarE id -> 
    (match (infer_match_name (get_typ_args exp.note) (gen_typ_name exp.note)) with
    | Some new_id -> T_app (T_ident [new_id; family_type_suffix], [T_ident [transform_var_id id]])
    | _ -> transform_exp exp
  )
  | CatE (exp1, exp2) -> T_app_infix (T_exp_basic T_listmatch, transform_match_exp exp1, transform_match_exp exp2)
  | IterE (exp, _) -> transform_match_exp exp
  | ListE exps -> (match exps with
    | [e] -> transform_match_exp e
    | _ -> transform_exp exp
  )
  | CaseE (m, e) -> (match (infer_match_name (get_typ_args exp.note) (gen_typ_name exp.note)) with 
    | Some a -> T_app (T_ident [a; family_type_suffix], [T_app (T_ident [a; transform_mixop m], transform_tuple_exp transform_match_exp e)])
    | _ -> transform_exp exp
  )
  | BinE (`AddOp, `NatT, exp1, {it = NumE (`Nat n);_}) -> let rec get_succ n = (match n with
    | 0 -> transform_match_exp exp1
    | m -> T_app (T_exp_basic T_succ, [get_succ (m - 1)])
  ) in get_succ (Z.to_int n)
  | _ -> transform_exp exp

and transform_tuple_exp (transform_func : exp -> coq_term) (exp : exp) = 
  match exp.it with
    | TupE exps -> List.map transform_func exps
    | _ -> [transform_func exp]


(* This is mainly a hack to make it coerce correctly with list types (only 1d lists) *)
(* This could be extended for other list expressions (and option), but for 1.0 this is fine *)
and transform_return_exp (r_typ : typ option) (exp : exp) = 
  match r_typ with
    | None -> transform_exp exp
    | Some typ -> (match exp.it with
      | ListE exps -> T_list (List.map (fun e -> T_cast ((transform_exp e), erase_dependent_type (remove_iter_typ typ))) exps)
      | _ -> transform_exp exp
    )

and transform_unop (u : unop) (exp : exp) = 
  match u with
    | `NotOp ->  T_app (T_exp_basic T_not, [transform_exp exp])
    | `PlusOp -> T_app_infix (T_exp_basic T_add, T_exp_basic (T_nat Z.zero), transform_exp exp)
    | `MinusOp -> T_app_infix (T_exp_basic T_sub, T_exp_basic (T_nat Z.zero), transform_exp exp)
    | `MinusPlusOp -> T_app (T_exp_basic T_minusplus, [transform_exp exp])
    | `PlusMinusOp -> T_app (T_exp_basic T_plusminus, [transform_exp exp])

and transform_binop (b : binop) = 
  match b with
    | `AndOp -> T_exp_basic T_and
    | `OrOp -> T_exp_basic T_or
    | `ImplOp -> T_exp_basic T_impl
    | `EquivOp -> T_exp_basic T_equiv
    | `AddOp -> T_exp_basic T_add
    | `SubOp -> T_exp_basic T_sub
    | `MulOp -> T_exp_basic T_mul
    | `DivOp -> T_exp_basic T_div
    | `PowOp -> T_exp_basic T_exp
    | `ModOp -> T_exp_basic T_mod

and transform_cmpop (c : cmpop) =
  match c with
    | `EqOp -> T_exp_basic T_eq
    | `NeOp -> T_exp_basic T_neq
    | `LtOp -> T_exp_basic T_lt
    | `GtOp -> T_exp_basic T_gt
    | `LeOp -> T_exp_basic T_le
    | `GeOp -> T_exp_basic T_ge

(* Binds, args, and params functions *)
and transform_arg (arg : arg) =
  match arg.it with
    | ExpA exp -> transform_exp exp
    | TypA typ -> erase_dependent_type typ
    | _ -> T_unsupported "" (* TODO *)

and transform_match_arg (arg : arg) =
  match arg.it with
    | ExpA exp -> transform_match_exp exp
    | TypA _ -> T_ident ["_"]
    | _ -> T_unsupported "" (* TODO *)

and transform_bind (bind : bind) =
  match bind.it with
    | ExpB (id, typ) -> (transform_var_id id, erase_dependent_type typ)
    | TypB id -> (transform_id id, T_ident ["Type"])
    | _ -> ("", T_unsupported "")

and transform_relation_bind (bind : bind) = (* TODO FIX relation binds to work as they used to *)
  (* let rec transform_iter_bind iters typ = (match iters with
    | [] -> typ
    | it :: its -> IterT (transform_iter_bind its typ, it) $ typ.at
  ) in *)
  match bind.it with
    | ExpB (id, ({it = VarT (t_id, args); _} as t)) -> 
      let id_transformed = transform_id t_id in 
      let a = find_typ args id_transformed in
        (transform_var_id id, (match a with
          | Some typ -> transform_type typ
          | None -> erase_dependent_type t
          (* | Some typ -> transform_type (transform_iter_bind (List.rev its) typ)
          | None -> erase_dependent_type (transform_iter_bind (List.rev its) t) *)
        ))
    | ExpB (id, typ) -> 
      (transform_var_id id, erase_dependent_type typ)
    | TypB id -> (transform_var_id id, T_ident ["Type"])
    | _ -> ("", T_unsupported "") (* TODO *)

and transform_param (arg : int * param) =
  let (n, p) = arg in 
  match p.it with
    | ExpP (id, typ) -> 
      (transform_var_id id ^ "_" ^ string_of_int n, erase_dependent_type typ)
    | TypP id -> transform_id id, T_ident ["Type"]
    | _ -> "", T_unsupported "" (* TODO *)

(* PATH Functions *)
and transform_list_path (p : path) = 
  match p.it with   
    | RootP -> []
    | IdxP (p', e') -> (IdxP (p', e') $$ (p.at, p.note)) :: transform_list_path p'
    | SliceP (p', _exp1, _exp2) -> (SliceP (p', _exp1, _exp2) $$ (p.at, p.note)) :: transform_list_path p'
    | DotP (p', a) -> (DotP (p', a) $$ (p.at, p.note)) :: transform_list_path p'

and gen_path_var_id (exp : exp) = 
  match exp.it with
    | VarE id -> Some (transform_var_id id)
    | _ -> None

(* TODO: Improve this handling for the case of two listlookups in a row *)
and transform_path (paths : path list) (n : int) (name : string option) = 
  let list_name num = (match name with
    | Some id -> id
    | None -> var_prefix ^ string_of_int num
  ) in
  match paths with
    | {it = DotP _; _} :: _ -> 
      let is_dot p = (match p.it with
        | DotP _ -> true
        | _ -> false 
      ) in
      let (dot_paths, rest) = list_split is_dot paths in 
      let projection_list = List.map (fun p -> match p.it with 
        | DotP (p, a) -> gen_typ_name p.note ^ "__" ^ transform_atom a
        | _ -> "" (* Should not happen *)
      ) dot_paths in
      P_recordlookup (projection_list, var_prefix ^ string_of_int n) :: transform_path rest (n + 1) (Some (String.concat " " projection_list ^ " " ^ list_name n))
    | {it = IdxP (_p', idx_exp); _} :: ps ->  P_listlookup (list_name (n - 1), transform_exp idx_exp) :: transform_path ps n None
    | {it = SliceP (_p', e1, e2); _} :: _ps -> [P_sliceupdate (list_name (n - 1), transform_exp e1, transform_exp e2)]
    | _ -> []

and transform_path_start (p : path) (start_name : exp) = 
  let paths = List.rev (transform_list_path p) in
  match paths with
    | [] -> error p.at "Path should not be empty"
    | _ -> transform_path paths 0 (gen_path_var_id start_name)

(* Premises *)
let rec transform_premise (p : prem) =
  match p.it with
    | IfPr exp -> P_if (transform_exp exp)
    | ElsePr -> P_else
    | LetPr _ -> P_unsupported ("LetPr: " ^ string_of_prem p)
    | IterPr (p, (iter, id_types)) -> let t_iter = if iter = Opt then I_option else I_list in
      P_listforall (t_iter, transform_premise p, List.map (fun (i, _typ) -> transform_var_id i) id_types)
    | RulePr (id, _mixop, exp) -> P_rule (transform_id id, transform_tuple_exp transform_exp exp)

let transform_deftyp (id : id) (binds : bind list) (deftyp : deftyp) =
  match deftyp.it with
    | AliasT typ -> if is_terminal_type typ then NotationD (transform_id id, transform_type typ) 
    else TypeAliasD (transform_id id, List.map transform_bind binds, erase_dependent_type typ)
    | StructT typfields -> RecordD (transform_id id, List.map (fun (a, (_, t, _), _) -> 
      (transform_id id ^ "__" ^ transform_atom a, erase_dependent_type t, Option.map (get_struct_type !env_ref) (get_typ_name t))
      ) typfields)
    | VariantT typcases -> InductiveD (transform_id id, List.map transform_bind binds, List.map (fun (m, (_, t, _), _) ->
        (transform_id id ^ "__" ^ transform_mixop m, transform_typ_args t)) typcases)

let transform_rule (id : id) (r : rule) = 
  match r.it with
    | RuleD (rule_id, binds, mixop, exp, premises) -> 
      ((transform_id id ^ "__" ^ transform_id rule_id ^ transform_mixop mixop, List.map transform_relation_bind binds), 
      List.map transform_premise premises, transform_tuple_exp transform_exp exp)

let transform_clause (return_type : typ option) (c : clause) =
  match c.it with
    | DefD (_binds, args, exp, _prems) -> (T_match (List.map transform_match_arg args), transform_return_exp return_type exp)

let transform_inst (id : id) (i : inst) =
  match i.it with
    | InstD (binds, _, deftyp) -> 
      let id_transformed = transform_id id in 
      let name = id_transformed ^ "__" ^ String.concat "__" (List.map gen_bind_name binds) in    
      Hashtbl.add family_helper id_transformed (VarT (id, []) $ i.at); (* Putting a dummy value as memcheck is only needed*)
      (name, (match deftyp.it with
      | AliasT typ -> 
        Hashtbl.add family_helper name typ;
        TypeAliasT (erase_dependent_type typ)
      | StructT _ -> error i.at "Family of records should not exist" (* This should never occur *)
      | VariantT typcases -> 
        Hashtbl.add family_helper name (VarT (id, []) $ i.at); (* Putting a dummy value as memcheck is only needed*)
        InductiveT (List.map (fun (m, (case_binds, _, _), _) -> (name ^ "__" ^ transform_mixop m, List.map transform_bind case_binds)) typcases))
    )

let rec transform_def (d : def) : coq_def =
  match d.it with
    | TypD (id, _, [{it = InstD (binds, _, deftyp);_}]) -> transform_deftyp id binds deftyp
    | TypD (id, _, insts) -> InductiveFamilyD (transform_id id, List.map (transform_inst id) insts)
    | RelD (id, _, typ, rules) -> InductiveRelationD (transform_id id, transform_tuple_to_relation_args typ, List.map (transform_rule id) rules)
    | DecD (id, params, typ, clauses) -> 
      let binds = List.map transform_param (List.combine (List.init (List.length params) (fun i -> i)) params) in 
      if (clauses == []) 
        then AxiomD (transform_fun_id id, binds, transform_return_type typ)
      else (
        let family_type_exists = List.fold_left (fun acc param -> acc || (match param.it with
          | ExpP (_, typ') -> check_family_dependent_type typ'
          | _ -> false
        )) false params in
        let new_clause = if family_type_exists then [(T_ident ["_"], T_ident ["default_val"])] else [] in
        let is_family_return_type = check_family_dependent_type typ in 
        let return_type = if is_family_return_type then transform_return_type typ else erase_dependent_type typ in 
        let base_return_type = if is_family_return_type then Some typ else None in 
        DefinitionD (transform_fun_id id, binds, return_type, (List.map (transform_clause base_return_type) clauses) @ new_clause)
      )
    | RecD defs -> MutualRecD (List.map transform_def defs)
    | _ -> UnsupportedD ""

let is_not_hintdef (d : def) : bool =
  match d.it with
    | HintD _ -> false
    | _ -> true 

(* -------------- Sub pass ----------------- *)

let sub_hastable = Hashtbl.create 16

let rec get_sube_exp (exp : exp) =
  match exp.it with
    | UnE (_, _, e) -> get_sube_exp e
    | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | TupE exps -> List.concat_map get_sube_exp exps
    | ProjE (e, _) -> get_sube_exp e
    | CaseE (_, e) -> get_sube_exp e
    | UncaseE (e, _) -> get_sube_exp e
    | OptE (Some e) -> get_sube_exp e
    | TheE e -> get_sube_exp e
    | StrE expfields -> List.concat_map (fun (_, e) -> get_sube_exp e) expfields
    | DotE (e, _) -> get_sube_exp e
    | CompE (e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | ListE exps -> List.concat_map get_sube_exp exps 
    | LenE e -> get_sube_exp e
    | CatE (e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | IdxE (e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | SliceE (e1, e2, e3) -> List.concat_map get_sube_exp [e1; e2; e3]
    | UpdE (e1, _, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | ExtE (e1, _, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | CallE (_, args) -> List.concat_map get_sube_arg args
    | IterE (e, _) -> get_sube_exp e
    | SubE _ as e -> [e $$ (exp.at, exp.note)]
    | _ -> []

and get_sube_arg (arg : arg) = 
  match arg.it with
    | ExpA e -> get_sube_exp e
    | TypA _ -> []
    | _ -> []

let rec get_sube_prem (premise : prem) =
  match premise.it with
    | RulePr (_, _, e) -> get_sube_exp e
    | IfPr e -> get_sube_exp e
    | IterPr (p, _) -> get_sube_prem p
    | _ -> []

let get_sube_rule (r : rule) =
  match r.it with
    | RuleD (_, _, _, e, prems) -> List.append (get_sube_exp e) (List.concat_map get_sube_prem prems)

let is_id_type (typ : typ) = 
  match typ.it with
    | VarT (_, args) -> args = []
    | _ -> false

let gen_typ_id (t : typ) =
  match t.it with
    | VarT (id, _) -> id
    | _ -> "" $ t.at

let rec is_same_type (t1 : typ) (t2 : typ) =
  match (t1.it, t2.it) with
    | VarT (id1, _), VarT (id2, _) -> id1.it = id2.it
    | NumT nt1, NumT nt2 -> nt1 = nt2
    | BoolT, BoolT -> true
    | TextT, TextT -> true
    | TupT tups, TupT tups2 -> (List.length tups) = (List.length tups2) && List.for_all2 (fun (_, t1') (_, t2') -> is_same_type t1' t2') tups tups2
    | IterT (t1', iter1), IterT (t2', iter2) -> iter1 = iter2 && is_same_type t1' t2'
    | _ -> false

(* Assumes that tuple variables will be in same order, can be modified if necessary *)
(* TODO must also check if some types inside the type are subtyppable and as such it should also be allowed *)
let rec find_same_typing (at : region) (m1 : ident) (t1 : typ) (t2_cases : sub_typ) =
  match t2_cases with
    | [] -> None
    | (_, m2, t2) as s_t :: _ when is_same_type t1 t2 && m1 = (transform_mixop m2) -> Some s_t
    | _ :: t2_cases' -> find_same_typing at m1 t1 t2_cases'

let get_num_tuple_typ (t : typ) = 
  match t.it with
    | TupT tups -> List.length tups 
    | _ -> 0

let transform_sub_types (at : region) (t1_id : id) (t2_id : id) (t1_cases : sub_typ) (t2_cases : sub_typ) =
  let func_name = func_prefix ^ coerce_prefix ^ transform_id t1_id ^ "__" ^ transform_id t2_id in 
  
  [Right (DefinitionD (func_name, 
    [(var_prefix ^ transform_id t1_id, T_ident [transform_id t1_id])],
    T_ident [transform_id t2_id], List.map (fun (id, m1, t1) ->
      let s_t = find_same_typing at (transform_mixop m1) t1 t2_cases in
      match s_t with
        | Some (id2, m2, _) ->
          let var_list = List.init (get_num_tuple_typ t1) (fun i -> T_ident [var_prefix ^ string_of_int i]) in
          (T_app (T_ident [transform_id id; transform_mixop m1], var_list),
          T_app (T_ident [transform_id id2; transform_mixop m2], var_list))
        | None -> (T_ident [""], T_ident [""])
    ) t1_cases)); 
  Right (CoercionD (func_name, transform_id t1_id, transform_id t2_id))]

(* TODO can be extended to other defs if necessary *)
let rec transform_sub_def (env : env) (d : def) = 
  match d.it with
    | RelD (_, _, _, rules) -> let sub_expressions = List.concat_map get_sube_rule rules in
      List.append (List.concat_map (fun e -> match e.it with 
        | SubE (_, t1, t2) when is_id_type t1 && is_id_type t2 -> 
          let (t1_id, t2_id) = (gen_typ_id t1, gen_typ_id t2) in
          let combined_name = (t1_id.it ^ "__" ^ t2_id.it) in 
          if (Hashtbl.mem sub_hastable combined_name) then []
          else (let typ1_cases = find "Sub pass" env.subs t1_id in
            let typ2_cases = find "Sub pass" env.subs t2_id in
            Hashtbl.add sub_hastable combined_name combined_name;
            transform_sub_types d.at t1_id t2_id typ1_cases typ2_cases)
        | _ -> []) sub_expressions) [Left d]
    | RecD defs -> let flat_list = List.concat_map (transform_sub_def env) defs in
      let (defs, coq_defs) = partition_eitherlist flat_list in
      (List.map Either.right coq_defs) @ [Left (RecD defs $ d.at)]
    | _ -> [Left d]

let transform_sub (e : env) (il : script) =
  List.concat_map (transform_sub_def e) il

(* Main transformation function *)
let transform (il : script) : coq_script =
  env_ref := Case.get_case_env il;
  let sub_transformed = transform_sub !env_ref il in
  List.filter_map (fun d -> 
    match d with 
      | Left def when is_not_hintdef def -> Some (transform_def def)
      | Right c_def -> Some c_def
      | _ -> None
  ) sub_transformed

