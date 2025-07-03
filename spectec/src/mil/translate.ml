open Il.Ast
open Il.Print
open Il.Free
open Ast
open Util
open Source

let error at msg = Error.error at "MIL Transformation" msg

let coerce_prefix = "coec_"
let var_prefix = "v_"
let fun_prefix = "fun_"
let reserved_prefix = "res_"
let wf_prefix = "wf_"
let make_prefix = "mk_"

let reserved_ids_set = ref Env.StringSet.empty
let env_ref = ref Il.Env.empty

let rec list_split (f : 'a -> bool) = function 
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

(* Id transformation *)
let transform_id' (prefix : text) (s : text) = 
  let s' = String.to_seq s |> Seq.take_while (fun c -> c != '*' && c != '?' && c != '^' ) |> String.of_seq in 
  match s' with
  | s when Env.StringSet.mem s !reserved_ids_set -> prefix ^ s
  | s -> String.map (function
     | '.' -> '_'
     | '-' -> '_'
     | c -> c
     ) s

let transform_var_id (id : id) = var_prefix ^ transform_id' "" id.it
let transform_fun_id (id : id) = fun_prefix ^ transform_id' "" id.it
let transform_user_def_id (id : id) = transform_id' reserved_prefix id.it
let transform_rule_id (id : id) (rel_id : id) = 
  match id.it with
    | "" -> make_prefix ^ rel_id.it
    | _ -> transform_id' reserved_prefix id.it

let transform_iter (iter : iter) =
  if iter = Opt then I_option else I_list

(* Identifier generation *)  
let gen_exp_name (e : exp) =
  match e.it with
    | VarE id -> transform_var_id id
    | _ -> "_" 
    
(* Atom functions *)
let transform_atom (a : atom) = 
  match a.it with
    | Atom s -> transform_user_def_id (s $ no_region)
    | _ -> ""

let is_atomid (a : atom) =
  match a.it with
    | Atom _ -> true
    | _ -> false

let transform_mixop (typ_id : id) (m : mixop) = 
  let str = (match m with
  | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> transform_user_def_id (a $ no_region) 
  | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )
  ) in
  match str with
    | "" -> make_prefix ^ typ_id.it
    | _ -> str

(* Type functions *)
let transform_itertyp (it : iter) =
  match it with
    | Opt -> T_type_basic T_opt
    | List | List1 | ListN _ -> T_type_basic T_list (* TODO think about ListN *)

let transform_numtyp (typ : numtyp) = 
  match typ with
    | `NatT -> T_type_basic T_nat
    | `IntT -> T_type_basic T_int
    | `RatT -> T_type_basic T_rat (*T_unsupported "rat"*)
    | `RealT -> T_type_basic T_real (*T_unsupported "real"*)

let rec transform_type (typ : typ) =
  match typ.it with
    | VarT (id, []) when not (Il.Env.mem_typ !env_ref id) -> 
      (* Must be a type parameter *)
      T_ident (transform_var_id id)
    | VarT (id, args) -> 
      let get_typ a = match a.it with
        | ExpA exp -> transform_type exp.note
        | TypA typ -> transform_type typ 
        | DefA _ | GramA _ -> assert false (* TODO Extend later *)
      in 
      let var_type = T_arrowtype (List.map get_typ args @ [T_type_basic T_anytype]) in
      T_app (T_ident (transform_user_def_id id), var_type, List.map transform_arg args)
    | BoolT -> T_type_basic T_bool
    | NumT nt -> transform_numtyp nt
    | TextT -> T_type_basic T_string 
    | TupT [] -> T_type_basic T_unit
    | TupT typs -> T_tupletype (List.map (fun (_, t) -> transform_type t) typs)
    | IterT (typ, iter) -> T_app (transform_itertyp iter, T_type_basic T_anytype, [transform_type typ])

and transform_typ_args (typ : typ) =
  match typ.it with
    | TupT [] -> []
    | TupT typs -> List.map (fun (e, t) -> (gen_exp_name e, transform_type t)) typs
    | _ -> [("_", transform_type typ)]

and transform_tuple_to_relation_args (t : typ) =
  match t.it with
    | TupT typs -> List.map (fun (_, t) -> transform_type t) typs
    | _ -> [transform_type t]

(* Expression functions *)
and transform_exp (exp : exp) =
  let typ = transform_type exp.note in
  match exp.it with 
    | VarE id -> T_ident (transform_var_id id)
    | BoolE b -> T_exp_basic (T_bool b)
    | NumE (`Nat n) -> T_exp_basic (T_nat n)
    | NumE (`Int i) -> T_exp_basic (T_int i)
    | NumE (`Rat r) -> T_exp_basic (T_rat r)
    | NumE (`Real r) -> T_exp_basic (T_real r)
    | TextE txt -> T_exp_basic (T_string txt)
    | UnE (unop, _, exp') -> transform_unop unop typ (transform_exp exp')
    | BinE (binop, _, exp1, exp2) -> T_app_infix (transform_binop binop, transform_exp exp1, transform_exp exp2)
    | CmpE (cmpop, _, exp1, exp2) -> T_app_infix (transform_cmpop cmpop, transform_exp exp1, transform_exp exp2)
    | TupE [] -> T_exp_basic T_exp_unit
    | TupE exps -> T_tuple (List.map transform_exp exps) 
    | ProjE (e, n) -> T_app (T_exp_basic T_listlookup, typ,[transform_exp e; T_exp_basic (T_nat (Z.of_int n))])
    | CaseE (mixop, e) ->
      let reduced_typ = Il.Eval.reduce_typ !env_ref exp.note in 
      let typ_id = string_of_typ_name reduced_typ $ no_region in
      T_app (T_ident (transform_mixop typ_id mixop), transform_type reduced_typ, transform_tuple_exp transform_exp e)
    | UncaseE (_e, _mixop) -> T_unsupported ("UncaseE: " ^ Il.Print.string_of_exp exp) (* Should be removed by preprocessing *)
    | OptE (Some e) -> T_app (T_exp_basic T_some, typ, [transform_exp e])
    | OptE None -> T_exp_basic T_none
    | TheE e -> T_app (T_exp_basic T_invopt, typ, [transform_exp e])
    | StrE expfields -> T_record_fields (List.map (fun (a, e) -> (transform_atom a, transform_exp e)) expfields)
    | DotE (e, atom) -> T_app (T_ident (transform_atom atom), typ, [transform_exp e])
    | CompE (exp1, exp2) -> T_app_infix (T_exp_basic T_recordconcat, transform_exp exp1, transform_exp exp2)
    | ListE exps -> T_list (List.map transform_exp exps)
    | LenE e -> T_app (T_exp_basic T_listlength, typ, [transform_exp e])
    | CatE (exp1, exp2) -> T_app_infix (T_exp_basic T_listconcat, transform_exp exp1, transform_exp exp2)
    | IdxE (exp1, exp2) -> T_app (T_exp_basic T_listlookup, typ, [transform_exp exp1; transform_exp exp2])
    | SliceE (exp1, exp2, exp3) -> T_app (T_exp_basic T_slicelookup, typ, [transform_exp exp1; transform_exp exp2; transform_exp exp3])
    | UpdE (exp1, path, exp2) -> transform_path_start' path (transform_exp exp1) false (transform_exp exp2) 
    | ExtE (exp1, path, exp2) -> transform_path_start' path (transform_exp exp1) true (transform_exp exp2)
    | CallE (id, args) -> T_app (T_ident (transform_fun_id id), typ, List.map transform_arg args)
    | IterE (exp, (iter, ids)) ->  
        let exp1 = transform_exp exp in
        (match iter, ids, exp.it with
        | (List | List1 | ListN _), [], _ -> T_list [exp1] 
        | Opt, [], _ -> T_app (T_exp_basic T_some, typ, [exp1])
        | (List | List1 | ListN _ | Opt), _, (VarE _ | IterE _) -> exp1 
        | Opt, [(_, _)], OptE (Some e) -> T_app (T_exp_basic T_some, typ, [transform_exp e])
        | (List | List1 | ListN _ | Opt), [(v, _)], _ -> T_app (T_exp_basic (T_map (transform_iter iter)), typ, [T_lambda ([transform_var_id v], exp1); T_ident (transform_var_id v)])
        | (List | List1 | ListN _ | Opt), [(v, _); (s, _)], _ -> T_app (T_exp_basic (T_zipwith (transform_iter iter)), typ, [T_lambda ([transform_var_id v; transform_var_id s], exp1); T_ident (transform_var_id v); T_ident (transform_var_id s)])
        | _ -> exp1
      )
    | SubE (e, typ1, typ2) -> T_cast (transform_exp e, transform_type typ1, transform_type typ2)
    | CvtE (e, numtyp1, numtyp2) -> T_cast (transform_exp e, transform_numtyp numtyp1, transform_numtyp numtyp2)
    | LiftE exp -> T_app (T_exp_basic T_opttolist, typ, [transform_exp exp])
    | MemE (e1, e2) -> T_app (T_exp_basic (T_listmember), T_type_basic T_bool, [transform_exp e1; transform_exp e2])

and transform_match_exp (exp : exp) =
  let typ = transform_type exp.note in 
  match exp.it with
  (* Specific match exp handling *)
  | CatE ({it = ListE [exp1]; _}, exp2) -> 
    T_app_infix (T_exp_basic T_listcons, transform_match_exp exp1, transform_match_exp exp2)
  | IterE (exp, _) -> transform_match_exp exp
  | BinE (`AddOp, _, exp1, {it = NumE (`Nat n) ;_}) -> let rec get_succ n = (match n with
    | 0 -> transform_match_exp exp1
    | m -> T_app (T_exp_basic T_succ, typ, [get_succ (m - 1)])
  ) in get_succ (Z.to_int n)
  (* Descend (TODO Maybe throw an error for specific constructs not allowed in matching?) *)
  | UnE (unop, _, exp) -> transform_unop unop typ (transform_match_exp exp)
  | BinE (binop, _, exp1, exp2) -> T_app_infix (transform_binop binop, transform_match_exp exp1, transform_match_exp exp2)
  | CmpE (cmpop, _, exp1, exp2) -> T_app_infix (transform_cmpop cmpop, transform_match_exp exp1, transform_match_exp exp2)
  | TupE [] -> T_exp_basic T_exp_unit
  | TupE exps -> T_match (List.map transform_match_exp exps) 
  | ProjE (e, n) -> T_app (T_exp_basic T_listlookup, typ, [transform_match_exp e; T_exp_basic (T_nat (Z.of_int n))])
  | CaseE (mixop, e) ->
    let typ_id = string_of_typ_name exp.note $ no_region in 
    T_app (T_ident (transform_mixop typ_id mixop), typ, transform_tuple_exp transform_match_exp e)
  | OptE (Some e) -> T_app (T_exp_basic T_some, typ, [transform_match_exp e])
  | OptE None -> T_exp_basic T_none
  | TheE e -> T_app (T_exp_basic T_invopt, typ, [transform_match_exp e])
  | StrE expfields -> T_record_fields (List.map (fun (a, e) -> (transform_atom a, transform_match_exp e)) expfields)
  | DotE (e, atom) -> T_app (T_ident (transform_atom atom), typ, [transform_match_exp e])
  | CompE (exp1, exp2) -> T_app_infix (T_exp_basic T_recordconcat, transform_match_exp exp1, transform_match_exp exp2)
  | LenE e -> T_app (T_exp_basic T_listlength, typ, [transform_match_exp e])
  | IdxE (exp1, exp2) -> T_app (T_exp_basic T_listlookup, typ, [transform_match_exp exp1; transform_match_exp exp2])
  | SliceE (exp1, exp2, exp3) -> T_app (T_exp_basic T_slicelookup, typ, [transform_match_exp exp1; transform_match_exp exp2; transform_match_exp exp3])
  | UpdE (exp1, path, exp2) -> transform_path_start' path (transform_match_exp exp1) false (transform_match_exp exp2) 
  | ExtE (exp1, path, exp2) -> transform_path_start' path (transform_match_exp exp1) true (transform_match_exp exp2)
  | CallE (id, args) -> T_app (T_ident (transform_fun_id id), typ, List.map transform_arg args)
  | SubE (e, typ1, typ2) -> T_cast (transform_exp e, transform_type typ1, transform_type typ2)
  | CvtE (e, numtyp1, numtyp2) -> T_cast (transform_exp e, transform_numtyp numtyp1, transform_numtyp numtyp2)
  | MemE (e1, e2) -> T_app (T_exp_basic (T_listmember), T_type_basic T_bool, [transform_match_exp e1; transform_match_exp e2])
  | LiftE exp -> T_app (T_exp_basic T_opttolist, typ, [transform_match_exp exp])
  | _ -> transform_exp exp

and transform_tuple_exp (transform_func : exp -> term) (exp : exp) = 
  match exp.it with
    | TupE exps -> List.map transform_func exps
    | _ -> [transform_func exp]

and transform_unop (u : unop) (typ : term) (exp : term) = 
  match u with
    | `NotOp ->  T_app (T_exp_basic T_not, typ, [exp])
    | `PlusOp -> T_app_infix (T_exp_basic T_add, T_exp_basic (T_nat Z.zero), exp)
    | `MinusOp -> T_app_infix (T_exp_basic T_sub, T_exp_basic (T_nat Z.zero), exp)

and transform_binop (b : binop)  = 
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
    | TypA typ -> transform_type typ
    | DefA id -> T_ident id.it 
    | GramA _ -> T_unsupported ("Grammar Arg: " ^ string_of_arg arg)

and transform_match_arg (arg : arg) =
  match arg.it with
    | ExpA exp -> transform_match_exp exp
    | TypA _ -> T_ident "_"
    | DefA id -> T_ident id.it
    | GramA _ -> T_unsupported ("Grammar Arg: " ^ string_of_arg arg)

and transform_bind (bind : bind) =
  match bind.it with
    | ExpB (id, typ) -> (transform_var_id id, transform_type typ)
    | TypB id -> (transform_var_id id, T_type_basic T_anytype)
    | DefB _ -> ("", T_unsupported ("Higher order func: " ^ string_of_bind bind))
    | GramB _ -> ("", T_unsupported ("Grammar bind: " ^ string_of_bind bind))

and transform_param (p : param) =
  match p.it with
    | ExpP (id, typ) -> 
      (transform_var_id id, transform_type typ)
    | TypP id -> transform_var_id id, T_type_basic T_anytype
    | DefP _ -> ("", T_unsupported ("Higher order func: " ^ string_of_param p))
    | GramP _ -> ("", T_unsupported ("Grammar param: " ^ string_of_param p))

(* PATH Functions *)
and transform_list_path (p : path) = 
  match p.it with   
    | RootP -> []
    | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) when p'.it = RootP -> []
    | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) -> p' :: transform_list_path p'

and transform_path_start' (p : path) name_term is_extend end_term  = 
  let paths = List.rev (p :: transform_list_path p) in
  transform_path' paths p.at 0 (Some name_term) is_extend end_term

and transform_path' (paths : path list) at n name is_extend end_term = 
  let is_dot p = (match p.it with
        | DotP _ -> true
        | _ -> false 
  ) in
  let term_typ typ = transform_type typ in
  let list_name num = (match name with
    | Some term -> term
    | None -> T_ident (var_prefix ^ string_of_int num)
  ) in
  (* TODO fix typing of newly created terms *)
  match paths with
    (* End logic for extend *)
    | [{it = IdxP (_, e); note; _}] when is_extend -> 
      let extend_term = T_app_infix (T_exp_basic T_listconcat, list_name n, end_term) in
      T_app (T_exp_basic T_listupdate, term_typ note, [list_name n; transform_exp e; T_lambda (["_"], extend_term)])
    | [{it = DotP (_, a); _}] when is_extend -> 
      let projection_term = T_app (T_ident (transform_atom a), T_type_basic T_anytype, [list_name n]) in
      let extend_term = T_app_infix (T_exp_basic T_listconcat, projection_term, end_term) in
      T_record_update (list_name n, T_ident (transform_atom a), extend_term)
    | [{it = SliceP (_, e1, e2); note; _}] when is_extend -> 
      let extend_term = T_app_infix (T_exp_basic T_listconcat, list_name n, end_term) in
      T_app (T_exp_basic T_sliceupdate, term_typ note, 
        [list_name n; transform_exp e1; transform_exp e2; T_lambda (["_"], extend_term)])
    (* End logic for update *)
    | [{it = IdxP (_, e); note; _}] -> 
      T_app (T_exp_basic T_listupdate, term_typ note, [list_name n; transform_exp e; T_lambda (["_"], end_term)])
    | [{it = DotP (_, a); _}] -> 
      T_record_update (list_name n, T_ident (transform_atom a), end_term)
    | [{it = SliceP (_, e1, e2); note; _}]  -> 
      T_app (T_exp_basic T_sliceupdate, term_typ note, 
        [list_name n; transform_exp e1; transform_exp e2; T_lambda (["_"], end_term)])
    (* Middle logic *)
    | {it = IdxP (_, e); note; _} :: ps -> 
      let path_term = transform_path' ps at (n + 1) None is_extend end_term in
      let new_name = var_prefix ^ string_of_int (n + 1) in 
      T_app (T_exp_basic T_listupdate, term_typ note, 
        [list_name n; transform_exp e; T_lambda ([new_name], path_term)])
    | {it = DotP (_, a); note = _; _} :: ps -> 
      let (dot_paths, ps') = list_split is_dot ps in 
      let projection_term = List.fold_right (fun p acc -> 
        match p.it with
          | DotP (_, a') -> T_app (T_ident (transform_atom a'), T_type_basic T_anytype, [acc])
          | _ -> error at "Should be a record access" (* Should not happen *)
      ) dot_paths (list_name n) in
      let new_term = T_app(T_ident (transform_atom a), T_type_basic T_anytype, [projection_term]) in
      let path_term = transform_path' ps' at n (Some new_term) is_extend end_term in
      T_record_update (projection_term, T_ident (transform_atom a), path_term)
    | {it = SliceP (_, e1, e2); note; _} :: ps ->
      let path_term = transform_path' ps at (n + 1) None is_extend end_term in
      let new_name = var_prefix ^ string_of_int (n + 1) in
      T_app (T_exp_basic T_sliceupdate, term_typ note, 
        [list_name n; transform_exp e1; transform_exp e2; T_lambda ([new_name], path_term)])
    (* Catch all error if we encounter empty list or RootP *)
    | _ -> error at "Paths should not be empty"

(* Premises *)
let rec transform_premise (p : prem) =
  match p.it with
    | IfPr exp -> P_if (transform_exp exp)
    | ElsePr -> P_else
    | LetPr (exp1, exp2, _) -> P_if (T_app_infix (T_exp_basic T_eq, transform_exp exp1, transform_exp exp2))
    | IterPr (p, (iter, [(id, _e)])) ->
      P_list_forall (transform_iter iter, transform_premise p, transform_var_id id)
    | IterPr (p, (iter, [(id, _e); (id2, _e2)])) ->
      P_list_forall2 (transform_iter iter, transform_premise p, transform_var_id id, transform_var_id id2)
    | IterPr _ -> P_unsupported (string_of_prem p) (* TODO could potentially extend this further if necessary *)
    | RulePr (id, _mixop, exp) -> P_rule (transform_user_def_id id, transform_tuple_exp transform_exp exp)

let transform_deftyp (id : id) (binds : bind list) (deftyp : deftyp) =
  match deftyp.it with
    | AliasT typ -> TypeAliasD (transform_user_def_id id, List.map transform_bind binds, transform_type typ)
    | StructT typfields -> RecordD (transform_user_def_id id, List.map (fun (a, (_, t, _), _) -> 
      (transform_atom a, transform_type t)) typfields)
    | VariantT typcases -> InductiveD (transform_user_def_id id, List.map transform_bind binds, List.map (fun (m, (_, t, _), _) ->
        (transform_mixop id m, transform_typ_args t)) typcases)

let transform_rule (id : id) (r : rule) = 
  match r.it with
    | RuleD (rule_id, binds, _mixop, exp, premises) -> 
      ((transform_rule_id rule_id id, List.map transform_bind binds), 
      List.map transform_premise premises, transform_tuple_exp transform_exp exp)

let transform_clause (fb : function_body option) (c : clause) =
  match c.it, fb with
    | DefD (_binds, args, exp, _prems), None -> (T_match (List.map transform_match_arg args), F_term (transform_exp exp))
    | DefD (_binds, args, _, _prems), Some fb -> (T_match (List.map transform_match_arg args), fb)

let transform_inst (id : id) (i : inst) =
  match i.it with
    | InstD (binds, args, deftyp) -> 
      let case_name = Tfamily.sub_type_name binds in
      let name_prefix = id.it ^ "_" in 
      match deftyp.it with
      | AliasT typ -> (Tfamily.type_family_prefix ^ name_prefix ^ case_name, List.map transform_bind binds @ [("_", transform_type typ)], List.map transform_arg args)
      | StructT _ -> error i.at "Family of records should not exist" (* This should never occur *)
      | VariantT _ -> 
        let binders = List.map transform_bind binds in 
        let terms = List.map (fun (name, _) -> T_ident name) binders in
        (Tfamily.type_family_prefix ^ name_prefix ^ case_name, binders @ [("_", 
        T_app (T_ident (id.it ^ case_name), T_type_basic T_anytype, terms))], List.map transform_arg args)

(* Inactive for now - need to understand well function defs with pattern guards *)
let _transform_clauses (clauses : clause list) : clause_entry list =
  let rec get_ids exp =
    match exp.it with
      | VarE id -> [id]
      | IterE (exp, _) -> get_ids exp
      | TupE exps -> let result = List.map get_ids exps in
        if List.exists List.is_empty result 
          then [] 
          else List.concat result
      | _ -> []
  in

  let modify_let_prems free_vars prems = 
    List.map (fun prem -> 
      match prem.it with
        | IfPr {it = CmpE(`EqOp, _, exp1, exp2); _} 
          when not (List.is_empty (get_ids exp1)) && not (List.exists (fun id -> Set.mem id.it free_vars.varid) (get_ids exp1)) -> 
            (LetPr (exp1, exp2, (free_exp exp1).varid |> Set.elements) $ prem.at)
        | IfPr {it = CmpE(`EqOp, _, exp1, exp2); _}
          when not (List.is_empty (get_ids exp2)) && not (List.exists (fun id -> Set.mem id.it free_vars.varid) (get_ids exp2)) ->
            (LetPr (exp2, exp1, (free_exp exp2).varid |> Set.elements) $ prem.at)
        | _ -> prem
      ) prems
  in

  let bigAndExp starting_exp exps = 
    List.fold_left (fun acc exp -> BinE (`AndOp, `BoolT, acc, exp) $$ exp.at % (BoolT $ exp.at)) starting_exp exps
  in
  
  let encode_prems acc_term otherwise prems =
    let rec go acc_bool acc_term otherwise prems =
      match prems with
        | [] -> (match acc_bool with
            | [] -> acc_term
            | e :: es -> F_if_else (transform_exp (bigAndExp e es), acc_term, otherwise)
          )
        | {it = IfPr exp; _} :: ps -> go (exp :: acc_bool) acc_term otherwise ps
        | {it = LetPr (exp1, exp2, _); _} :: ps -> go acc_bool (F_let (transform_exp exp1, transform_exp exp2, acc_term)) otherwise ps
        | _ :: ps -> go acc_bool acc_term otherwise ps
      in
    go [] acc_term otherwise prems
  in

  let rec rearrange_clauses clauses = 
    match clauses with
      | [] -> []
      | ({it = DefD(_, args, exp, prems); _} as clause) :: cs ->
        let (same_args, rest) = list_split (fun c -> match c.it with
          | DefD(_, args', _, _) -> Il.Eq.eq_list Il.Eq.eq_arg args args'
        ) cs in
        (match List.rev (clause :: same_args) with
          | [] -> assert false (* Impossible to get to *)
          | [_] -> 
            transform_clause (Some (encode_prems (F_term (transform_exp exp)) F_default (List.rev prems))) clause 
          | {it = DefD(_, _, exp', _); _} :: rev_tail -> 
            let starting_fb = F_term (transform_exp exp') in
            let fb = List.fold_left (fun acc clause' -> match clause'.it with
              | DefD(_, _, exp'', prems'') -> encode_prems (F_term (transform_exp exp'')) acc (List.rev prems'') 
            ) starting_fb rev_tail in 
            transform_clause (Some fb) clause
        ) :: rearrange_clauses rest
      
  in
  
  List.map (fun clause -> match clause.it with 
    | DefD(binds, args, exp, prems) -> DefD(binds, args, exp, modify_let_prems (free_list free_arg args) prems) $ clause.at
  ) clauses 
  |> rearrange_clauses

let create_well_formed_function id params inst =
  let get_typ_args_ids (typ : typ) = match typ.it with
    | TupT tups -> List.map fst tups 
    | _ -> []
  in 
  match inst.it with
    | InstD (_ , _, {it = VariantT typcases; _}) when List.for_all (fun (_, (_, _, prems), _) -> List.is_empty prems) typcases -> 
      (* Case with no premises, does not need well-formedness *)
      None
    | InstD (_, _, {it = VariantT typcases; _}) -> 
      let user_typ = VarT (id, List.map Preprocess.make_arg params) $ no_region in 
      let new_param = ExpP ("x" $ no_region, user_typ) $ no_region in
      let new_params = params @ [new_param] in 
      let clauses = List.map (fun (m, (binds, typ, prems), _) -> 
        let case_typs = Preprocess.get_case_typs typ in   
        let new_var_exps = List.mapi (fun _idx (e, _t) -> e) case_typs in 
        let new_tup = TupE (new_var_exps) $$ no_region % (TupT case_typs $ no_region) in
        let new_case_exp = CaseE(m, new_tup) $$ no_region % user_typ in
        let new_arg = ExpA new_case_exp $ no_region in 
        let new_args = List.map Preprocess.make_arg params @ [new_arg] in
        let free_vars = (free_list free_exp (get_typ_args_ids typ)).varid in
        let filtered_binds = List.filter (fun b -> match b.it with
          | ExpB (id', _) -> not (Set.mem id'.it free_vars) 
          | _ -> false
        ) binds in
        (T_match (List.map transform_match_arg new_args), F_premises (List.map transform_bind filtered_binds, List.map transform_premise prems))
      ) typcases in
      Some (DefinitionD (wf_prefix ^ id.it, List.map transform_param new_params, T_type_basic T_prop, clauses))
    | _ -> None

(* Generates a fresh name if necessary, and goes up to a maximum which then it will return an error*)
let generate_var at ids i =
  (* TODO - could make these variables a record type to make it configurable *) 
  let start = 0 in
  let fresh_prefix = "var" in
  let max = 100 in
  let rec go id c =
    if max <= c then error at "Reached max variable generation" else
    let name = id ^ "_" ^ Int.to_string c in 
    if (List.mem name ids) 
      then go id (c + 1) 
      else name
  in
  match i with
    | "" | "_" -> go fresh_prefix start
    | s when List.mem s ids -> go i start
    | _ -> i

let improve_ids_params (params : param list) : param list = 
  let get_id p = match p.it with
    | ExpP (id, _) -> id.it
    | TypP id -> id.it
    | DefP (id, _, _) -> id.it
    | GramP (id, _) -> id.it
  in
  let construct_with_name p name = (match p.it with 
    | ExpP (id, typ) -> ExpP(name $ id.at, typ)
    | TypP id -> TypP (name $ id.at)
    | DefP (id, params, typ) -> DefP(name $ id.at, params, typ)
    | GramP (id, typ) -> GramP (name $ id.at, typ)) $ p.at
  in
  let rec improve_ids_helper ids ps = 
    match ps with
      | [] -> []
      | p :: ps' -> 
        let p_id = get_id p in 
        let new_name = generate_var p.at ids p_id in 
        construct_with_name p new_name :: improve_ids_helper (new_name :: ids) ps'
  in
  improve_ids_helper [] params

let rec transform_def (def : def) : mil_def list =
  let has_prems clause = match clause.it with
    | DefD (_, _, _, prems) -> prems <> []
  in
  (match def.it with
    | TypD (id, params, [({it = InstD (binds, _, deftyp);_} as inst)]) 
      when Tfamily.check_normal_type_creation inst -> 
      let wf_func = Option.to_list (create_well_formed_function id params inst) in 
      transform_deftyp id binds deftyp :: wf_func 
    | TypD (id, params, insts) -> [InductiveFamilyD (transform_user_def_id id, List.map (fun p -> snd (transform_param p)) params, List.map (transform_inst id) insts)]
    | RelD (id, _, typ, rules) -> [InductiveRelationD (transform_user_def_id id, transform_tuple_to_relation_args typ, List.map (transform_rule id) rules)]
    | DecD (id, params, typ, clauses) ->
      let improved_params = improve_ids_params params in  
      (match improved_params, clauses with
        | _, [] -> 
          (* No implementation - resorts to being an axiom *)
          [AxiomD (transform_fun_id id, List.map transform_param improved_params, transform_type typ)]
        | [], [clause] ->
          (* With one clause and no params - this is essentially a global variable *)
          [GlobalDeclarationD (transform_fun_id id, transform_type typ, transform_clause None clause)]
        | _, clauses when List.exists has_prems clauses -> 
          (* HACK - Need to deal with premises in the future. *)
          [AxiomD (transform_fun_id id, List.map transform_param improved_params, transform_type typ)]
        | _ -> 
          (* Normal function *)
          [DefinitionD (transform_fun_id id, List.map transform_param improved_params, transform_type typ, List.map (transform_clause None) clauses)]
      )
    | RecD defs -> [MutualRecD (List.concat_map transform_def defs)]
    | HintD _ | GramD _ -> [UnsupportedD (string_of_def def)]
  ) |> List.map (fun d -> d $ def.at)

let is_not_hintdef (d : def) : bool =
  match d.it with
    | HintD _ -> false
    | _ -> true 

(* Main transformation function *)
let transform (reserved_ids : Env.StringSet.t) (il : script) : mil_script =
  reserved_ids_set := reserved_ids; 
  let preprocessed_il = Preprocess.preprocess il in
  env_ref := Il.Env.env_of_script preprocessed_il;
  List.filter is_not_hintdef preprocessed_il |>
  List.concat_map transform_def 