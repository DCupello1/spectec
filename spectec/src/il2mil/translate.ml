open Il.Ast
open Il.Print
open Il.Free
open Mil.Ast
open Mil.Utils
open Util
open Source

module StringMap = Map.Make(String)

type exp_type =
  | MATCH
  | RELATION
  | NORMAL
  
let error at msg = Error.error at "MIL Transformation" msg

let coerce_prefix = "coec_"
let var_prefix = "v_"
let fun_prefix = "fun_"
let reserved_prefix = "res_"
let wf_prefix = "wf_"
let make_prefix = "mk_"

let reserved_ids_set = ref StringSet.empty
let env_ref = ref Il.Env.empty

let rec list_split (f : 'a -> bool) = function 
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

(* Id transformation *)
let transform_id' (prefix : text) (s : text) = 
  let change_id s' = 
    String.map (function
     | '.' -> '_'
     | '-' -> '_'
     | c -> c
    ) s'
    (* This suffixes any '*' or '^' with '_lst' and '?' with '_opt' for clarity *)
    |> Str.global_replace (Str.regexp {|\([*|^]\)|}) "_lst"
    |> Lib.String.replace "?" "_opt"
    (* This matches any string that has a name with an apostrophe and ensures that the added suffixes are placed before it 
    * i.e. "val'*" will turn into "val_lst'" 
    *)
    |> Str.global_replace (Str.regexp {|\([a-zA-Z]+\)\('*\)\(.+\)|}) "\\1\\3\\2"
  in
  match s with
  | s when StringSet.mem s !reserved_ids_set -> prefix ^ change_id s
  | s -> change_id s

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
  | IterE ({it = VarE id; _}, (iter, _)) -> transform_var_id (id.it ^ string_of_iter iter $ id.at)
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

let transform_mixop (typ_id : string) (m : mixop) = 
  let str = (match m with
    | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> transform_user_def_id (a $ no_region) 
    | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )
  ) in
  match str with
  | "" -> make_prefix ^ typ_id
  | _ -> str

let atom_string_combine a typ_name = string_combine (transform_atom a) typ_name

let mixop_string_combine m typ_name = string_combine (transform_mixop typ_name m) typ_name

let remove_iterT (t : typ) = 
  match t.it with
  | IterT (typ, _) -> typ
  | _ -> t

(* Type functions *)
let transform_itertyp (it : iter) =
  (match it with
  | Opt -> T_type_basic T_opt
  | List | List1 | ListN _ -> T_type_basic T_list
  ) $@ anytype'
  (* TODO think about ListN *)

let transform_numtyp (typ : numtyp) = 
  match typ with
  | `NatT -> T_type_basic T_nat
  | `IntT -> T_type_basic T_int
  | `RatT -> T_type_basic T_rat (*T_unsupported "rat"*)
  | `RealT -> T_type_basic T_real (*T_unsupported "real"*)

let rec transform_type exp_type (typ : typ): term = 
  transform_type' exp_type typ $@ anytype'

and transform_type' exp_type (typ : typ): mil_typ =
  match typ.it with
  | VarT (id, []) when not (Il.Env.mem_typ !env_ref id) -> 
    (* Must be a type parameter *)
    T_ident (transform_var_id id)
  | VarT (id, args) -> 
    let var_type = T_arrowtype ((List.map (get_typ_from_arg exp_type) args) @ [anytype']) in
    T_app (T_ident (transform_user_def_id id) $@ var_type, List.map (transform_arg exp_type) args)
  | BoolT when exp_type = RELATION -> T_type_basic T_prop
  | BoolT -> T_type_basic T_bool
  | NumT nt -> transform_numtyp nt
  | TextT -> T_type_basic T_string
  | TupT [] -> T_type_basic T_unit
  | TupT typs -> T_tupletype (List.map (fun (_, t) -> transform_type' exp_type t) typs) 
  | IterT (typ, iter) -> T_app (transform_itertyp iter, [transform_type exp_type typ])

and get_typ_from_arg exp_type a = 
  match a.it with
  | ExpA exp -> transform_type' exp_type exp.note
  | TypA typ -> transform_type' exp_type typ 
  | DefA _ | GramA _ -> assert false (* TODO Extend later *)
  
and transform_typ_args exp_type (typ : typ) =
  match typ.it with
  | TupT [] -> []
  | TupT typs -> List.map (fun (e, t) -> (gen_exp_name e, transform_type' exp_type t)) typs
  | _ -> [("_", transform_type' exp_type typ)]

and transform_tuple_to_relation_args exp_type (t : typ) =
  match t.it with
  | TupT typs -> List.map (fun (_, t) -> transform_type' exp_type t) typs
  | _ -> [transform_type' exp_type t]

(* Expression functions *)
and transform_exp exp_type (exp : exp) =
  let exp_typ = transform_type' exp_type exp.note in
  match exp.it with 
  | CatE ({it = ListE [exp1]; _}, exp2) when exp_type = MATCH ->
    let listcons_typ = T_arrowtype [transform_type' exp_type exp1.note; 
      transform_type' exp_type exp2.note; 
      exp_typ] in
    T_app_infix (T_exp_basic T_listcons $@ listcons_typ, transform_exp exp_type exp1, transform_exp exp_type exp2) $@ exp_typ
  | IterE (exp', _) when exp_type = MATCH  -> (transform_exp exp_type exp').it $@ exp_typ
  | BinE (`AddOp, _, exp1, {it = NumE (`Nat n) ;_}) when exp_type = MATCH  -> 
    let rec get_succ n = (match n with
    | 0 -> (transform_exp exp_type exp1)
    | m -> 
      let succtyp = T_arrowtype [T_type_basic T_nat; T_type_basic T_nat] in
      T_app (T_exp_basic T_succ $@ succtyp, [get_succ (m - 1)]) $@ T_type_basic T_nat
    ) in (get_succ (Z.to_int n)).it $@ exp_typ
  | SubE (e, _typ1, typ2) when exp_type = MATCH  -> (transform_exp exp_type e).it $@ (transform_type' exp_type typ2)
  | VarE id -> T_ident (transform_var_id id) $@ exp_typ
  | BoolE b -> T_exp_basic (T_bool b) $@ exp_typ
  | NumE (`Nat n) -> T_exp_basic (T_nat n) $@ exp_typ
  | NumE (`Int i) -> T_exp_basic (T_int i) $@ exp_typ
  | NumE (`Rat r) -> T_exp_basic (T_rat r) $@ exp_typ
  | NumE (`Real r) -> T_exp_basic (T_real r) $@ exp_typ
  | TextE txt -> T_exp_basic (T_string txt) $@ exp_typ
  | UnE (unop, op, exp') -> transform_unop exp.at unop op (transform_exp exp_type exp') $@ exp_typ
  | BinE (binop, optyp, exp1, exp2) -> T_app_infix (transform_binop exp_type exp.at binop optyp, transform_exp exp_type exp1, transform_exp exp_type exp2) $@ exp_typ
  | CmpE (cmpop, optyp, exp1, exp2) -> 
    let typ1 = transform_type' exp_type exp1.note in
    let typ2 = transform_type' exp_type exp2.note in
    T_app_infix (
    transform_cmpop exp_type exp.at cmpop optyp typ1 typ2, 
    transform_exp exp_type exp1, 
    transform_exp exp_type exp2) $@ exp_typ
  | TupE [] -> T_exp_basic T_exp_unit $@ exp_typ
  | TupE exps -> T_tuple (List.map (transform_exp exp_type) exps) $@ exp_typ
  | ProjE (_e, _n) -> T_unsupported (Il.Print.string_of_exp exp) $@ exp_typ
    (* T_app (T_exp_basic T_listlookup $@ anytype', [transform_exp exp_type e; T_exp_basic (T_nat (Z.of_int n)) $@ T_type_basic T_nat]) *)
  | CaseE (mixop, e) ->
    let reduced_typ = Il.Eval.reduce_typ !env_ref exp.note in 
    let typ_id = string_of_typ_name reduced_typ $ no_region in
    T_caseapp (([], transform_mixop typ_id.it mixop), transform_tuple_exp (transform_exp exp_type) e) $@ (transform_type' exp_type reduced_typ)
  | UncaseE (_e, _mixop) -> T_unsupported ("UncaseE: " ^ Il.Print.string_of_exp exp) $@ exp_typ (* Should be removed by preprocessing *)
  | OptE (Some e) ->
    let typ' = transform_type' exp_type e.note in
    let sometyp = T_arrowtype [typ'; exp_typ] in
    T_app (T_exp_basic T_some $@ sometyp, [transform_exp exp_type e]) $@ exp_typ
  | OptE None -> T_exp_basic T_none $@ exp_typ
  | TheE e -> 
    let typ' = transform_type' exp_type e.note in
    let invtyp = T_arrowtype [typ'; exp_typ] in
    T_app (T_exp_basic T_invopt $@ invtyp, [transform_exp exp_type e]) $@ exp_typ
  | StrE expfields -> T_record_fields (List.map (fun (a, e) -> (([], transform_atom a), transform_exp exp_type e)) expfields) $@ exp_typ
  | DotE (e, atom) -> 
    T_dotapp (([], transform_atom atom), transform_exp exp_type e) $@ exp_typ
  | CompE (exp1, exp2) -> 
    let comptyp = T_arrowtype [transform_type' exp_type exp1.note; transform_type' exp_type exp2.note; exp_typ] in
    T_app_infix (T_exp_basic T_recordconcat $@ comptyp, transform_exp exp_type exp1, transform_exp exp_type exp2) $@ exp_typ
  | ListE exps -> T_list (List.map (transform_exp exp_type) exps) $@ exp_typ
  | LenE e -> 
    let lentyp = T_arrowtype [transform_type' exp_type e.note; T_type_basic T_nat] in
    T_app (T_exp_basic T_listlength $@ lentyp, [transform_exp exp_type e]) $@ exp_typ
  | CatE (exp1, exp2) -> 
    let cattyp = T_arrowtype [transform_type' exp_type exp1.note; transform_type' exp_type exp2.note; exp_typ] in
    T_app_infix (T_exp_basic T_listconcat $@ cattyp, transform_exp exp_type exp1, transform_exp exp_type exp2) $@ exp_typ
  | IdxE (exp1, exp2) -> 
    let typ1 = transform_type' exp_type exp1.note in
    let idxtyp = T_arrowtype [typ1; transform_type' exp_type exp2.note; exp_typ] in
    T_app (T_exp_basic T_listlookup $@ idxtyp, [transform_exp exp_type exp1; transform_exp exp_type exp2]) $@ exp_typ
  | SliceE (exp1, exp2, exp3) -> 
    let typ1 = transform_type' exp_type exp1.note in
    let slicetyp = T_arrowtype [typ1; transform_type' exp_type exp2.note; transform_type' exp_type exp3.note; exp_typ] in
    T_app (T_exp_basic T_slicelookup $@ slicetyp, [transform_exp exp_type exp1; transform_exp exp_type exp2; transform_exp exp_type exp3]) $@ exp_typ
  | UpdE (exp1, path, exp2) -> 
    transform_path_start' path (transform_exp exp_type exp1) false (transform_exp exp_type exp2) $@ exp_typ
  | ExtE (exp1, path, exp2) -> transform_path_start' path (transform_exp exp_type exp1) true (transform_exp exp_type exp2) $@ exp_typ
  | CallE (id, args) -> 
    let fun_type = T_arrowtype ((List.map (get_typ_from_arg exp_type) args) @ [exp_typ]) in
    T_app (T_ident (transform_fun_id id) $@ fun_type, List.map (transform_arg exp_type) args) $@ exp_typ
  | IterE (exp1, (iter, ids)) ->  
    let term1 = transform_exp exp_type exp1 in
    let term1_typ = transform_type' exp_type exp1.note in
    (match iter, ids, exp1.it with
    | ListN (n, None), [], _ -> 
      let n_typ = transform_type' exp_type n.note in
      let sometyp = T_arrowtype [term1_typ; n_typ; exp_typ] in
      T_app(T_exp_basic T_listrepeat $@ sometyp, [term1; (transform_exp exp_type n)])
    (* Look into implementing a special case for when there is an id *)
    | (List | List1 | ListN _), [], _ -> 
      T_list [term1] 
    | Opt, [], _ ->
      let sometyp = T_arrowtype [term1_typ; exp_typ] in
      T_app (T_exp_basic T_some $@ sometyp, [transform_exp exp_type exp1])
    | Opt, [_], OptE (Some e) -> 
      let typ' = transform_type' exp_type e.note in
      let sometyp = T_arrowtype [typ'; exp_typ] in
      T_app (T_exp_basic T_some $@ sometyp, [transform_exp exp_type e])
    | (List | List1 | ListN _ | Opt), _, (VarE var_id) ->
      (* Still considered a list type so no need to modify type *) 
      T_ident (transform_var_id (var_id.it ^ string_of_iter iter $ var_id.at))
    | (List | List1 | ListN _ | Opt), [(v, {it = VarE v_list_id; note = v_typ; _})], _ -> 
      let typ1 = transform_type' exp_type v_typ in
      let res_typ_iter = (transform_type' exp_type exp.note) in
      let res_type = remove_iter_from_type res_typ_iter in
      let vartyp1 = remove_iter_from_type typ1 in
      let lambda_typ = T_arrowtype [vartyp1; res_type] in
      let map_typ = T_arrowtype [lambda_typ; typ1; res_typ_iter] in
      T_app (T_exp_basic (T_map (transform_iter iter)) $@ map_typ, [T_lambda ([(transform_var_id v, vartyp1)], term1) $@ lambda_typ; T_ident (transform_var_id v_list_id) $@ typ1])
    | (List | List1 | ListN _ | Opt), [(v, {it = VarE v_list_id; note = v_typ; _}); (s, {it = VarE s_list_id; note = s_typ; _})], _ -> 
      let typ1 = transform_type' exp_type v_typ in
      let typ2 = transform_type' exp_type s_typ in
      let res_typ_iter = (transform_type' exp_type exp.note) in
      let res_type = remove_iter_from_type res_typ_iter in
      let vartyp1 = remove_iter_from_type typ1 in
      let vartyp2 = remove_iter_from_type typ2 in
      let lambda_typ = T_arrowtype [vartyp1; vartyp2; res_type] in
      let zipwith_typ = T_arrowtype [lambda_typ; typ1; typ2; res_typ_iter] in
      T_app (T_exp_basic (T_zipwith (transform_iter iter)) $@ zipwith_typ, [T_lambda ([(transform_var_id v, vartyp1); (transform_var_id s, vartyp2)], term1) $@ lambda_typ; T_ident (transform_var_id v_list_id) $@ typ1; T_ident (transform_var_id s_list_id) $@ typ2])
    | _ -> term1.it) $@ exp_typ
  | SubE (e, typ1, typ2) -> T_cast (transform_exp exp_type e, transform_type' exp_type typ1, transform_type' exp_type typ2) $@ exp_typ
  | CvtE (e, numtyp1, numtyp2) -> T_cast (transform_exp exp_type e, transform_numtyp numtyp1, transform_numtyp numtyp2) $@ exp_typ
  | LiftE exp ->
    let opt_typ = T_app (transform_itertyp Opt, [transform_exp exp_type exp]) in
    let opttolisttyp = T_arrowtype [opt_typ; exp_typ] in
    T_app (T_exp_basic T_opttolist $@ opttolisttyp, [transform_exp exp_type exp]) $@ exp_typ
  | MemE (e1, e2) -> 
    let memtyp = T_arrowtype [transform_type' exp_type e1.note; transform_type' exp_type e2.note; exp_typ] in
    T_app (T_exp_basic (T_listmember) $@ memtyp, [transform_exp exp_type e1; transform_exp exp_type e2]) $@ exp_typ


and transform_tuple_exp (transform_func : exp -> term) (exp : exp) = 
  match exp.it with
  | TupE exps -> List.map transform_func exps
  | _ -> [transform_func exp]

and transform_unop (at : region) (u : unop) (op : optyp) (exp : term) = 
  match u, op with
  | `NotOp, _ ->  
    let not_typ = T_arrowtype [T_type_basic T_bool; T_type_basic T_bool] in
    T_app (T_exp_basic T_not $@ not_typ, [exp])
  | `PlusOp, (#Xl.Num.typ as nt) -> T_app_infix (
    T_exp_basic T_add $@ num_typ (transform_numtyp nt), 
    T_exp_basic (T_nat Z.zero) $@ transform_numtyp nt, exp)
  | `MinusOp, (#Xl.Num.typ as nt) -> T_app_infix (
    T_exp_basic T_sub $@ num_typ (transform_numtyp nt), 
    T_exp_basic (T_nat Z.zero) $@ transform_numtyp nt, exp)
  | _, _ -> error at "Malformed unary operation"

and transform_binop (exp_type : exp_type) (at : region) (b : binop) (op: optyp) = 
  let logoptyp = if exp_type = RELATION then prop_binop_typ else bool_binop_typ in  
  match b, op with
  | `AndOp, _ -> T_exp_basic T_and $@ logoptyp
  | `OrOp, _ -> T_exp_basic T_or $@ logoptyp
  | `ImplOp, _ -> T_exp_basic T_impl $@ logoptyp
  | `EquivOp, _ -> T_exp_basic T_equiv $@ logoptyp
  | `AddOp, (#Xl.Num.typ as nt) -> T_exp_basic T_add $@ num_typ (transform_numtyp nt)
  | `SubOp, (#Xl.Num.typ as nt) -> T_exp_basic T_sub $@ num_typ (transform_numtyp nt)
  | `MulOp, (#Xl.Num.typ as nt) -> T_exp_basic T_mul $@ num_typ (transform_numtyp nt)
  | `DivOp, (#Xl.Num.typ as nt) -> T_exp_basic T_div $@ num_typ (transform_numtyp nt)
  | `PowOp, (#Xl.Num.typ as nt) -> T_exp_basic T_exp $@ num_typ (transform_numtyp nt)
  | `ModOp, (#Xl.Num.typ as nt) -> T_exp_basic T_mod $@ num_typ (transform_numtyp nt) 
  | _, _ -> error at "Malformed binary operation"

and transform_cmpop (exp_type : exp_type) (at : region) (c : cmpop) (op : optyp) (t1 : term') (t2 : term') =
  let cmptyp = if exp_type = RELATION then T_type_basic T_prop else T_type_basic T_bool in 
  let cmpnum_typ nt = T_arrowtype [nt; nt; cmptyp] in
  match c, op with
  | `EqOp, _ -> 
    let typ = T_arrowtype [t1; t2; cmptyp] in
    T_exp_basic T_eq $@ typ
  | `NeOp, _ -> 
    let typ = T_arrowtype [t1; t2; cmptyp] in
    T_exp_basic T_neq $@ typ
  | `LtOp, (#Xl.Num.typ as nt) -> 
    T_exp_basic T_lt $@ cmpnum_typ (transform_numtyp nt)
  | `GtOp, (#Xl.Num.typ as nt) -> 
    T_exp_basic T_gt $@ cmpnum_typ (transform_numtyp nt)
  | `LeOp, (#Xl.Num.typ as nt) -> 
    T_exp_basic T_le $@ cmpnum_typ (transform_numtyp nt)
  | `GeOp, (#Xl.Num.typ as nt) -> 
    T_exp_basic T_ge $@ cmpnum_typ (transform_numtyp nt)
  | _, _ -> error at "Malformed comparison operation"

(* Binds, args, and params functions *)
and transform_arg exp_type (arg : arg) =
  match arg.it with
  | ExpA exp -> transform_exp exp_type exp
  | TypA typ when exp_type = MATCH -> T_ident "_" $@ (transform_type' exp_type typ)
  | TypA typ -> transform_type exp_type typ
  | DefA id -> T_ident id.it $@ anytype'
  | GramA _ -> T_unsupported ("Grammar Arg: " ^ string_of_arg arg) $@ anytype'

and transform_bind (bind : bind) =
  match bind.it with
  | ExpB (id, typ) -> (transform_var_id id, transform_type' NORMAL typ)
  | TypB id -> (transform_var_id id, anytype')
  | DefB _ -> ("", T_unsupported ("Higher order func: " ^ string_of_bind bind))
  | GramB _ -> ("", T_unsupported ("Grammar bind: " ^ string_of_bind bind))

and transform_param (p : param) =
  match p.it with
  | ExpP (id, typ) -> 
    (transform_var_id id, transform_type' NORMAL typ)
  | TypP id -> transform_var_id id, anytype'
  | DefP _ -> ("", T_unsupported ("Higher order func: " ^ string_of_param p))
  | GramP _ -> ("", T_unsupported ("Grammar param: " ^ string_of_param p))

(* PATH Functions *)
and transform_list_path (p : path) = 
  match p.it with   
  | RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) when p'.it = RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) -> p' :: transform_list_path p'

and transform_path_start' (p : path) name_term is_extend end_term = 
  let paths = List.rev (p :: transform_list_path p) in
  (transform_path' paths (name_term.typ) p.at 0 (Some name_term) is_extend end_term)

and transform_path' (paths : path list) typ at n name is_extend end_term = 
  let is_dot p = (match p.it with
    | DotP _ -> true
    | _ -> false 
  ) in
  let list_name num = (match name with
    | Some term -> term
    | None -> T_ident (var_prefix ^ string_of_int num) $@ typ
  ) in

  let new_name_typ = remove_iter_from_type (list_name n).typ in
  let new_name = var_prefix ^ string_of_int (n + 1) in 
  (* TODO fix typing of newly created terms *)
  match paths with
  (* End logic for extend *)
  | [{it = IdxP (_, e); _}] when is_extend -> 
    let extend_term = T_app_infix (T_exp_basic T_listconcat $@ anytype', T_ident new_name $@ new_name_typ, end_term) $@ new_name_typ in
    let lambda_typ = T_arrowtype [new_name_typ; new_name_typ] in
    T_app (T_exp_basic T_listupdate $@ anytype',  [list_name n; transform_exp NORMAL e; T_lambda ([new_name, new_name_typ], extend_term) $@ lambda_typ])
  | [{it = DotP (_, a); note; _ }] when is_extend -> 
    let projection_term = T_dotapp (([], transform_atom a), list_name n) $@ transform_type' NORMAL note in
    let extend_term = T_app_infix (T_exp_basic T_listconcat $@ anytype', projection_term, end_term) $@ end_term.typ in
    T_record_update (list_name n, ([], transform_atom a), extend_term)
  | [{it = SliceP (_, e1, e2); _}] when is_extend -> 
    let extend_term = T_app_infix (T_exp_basic T_listconcat $@ anytype', T_ident new_name $@ new_name_typ, end_term) $@ new_name_typ in
    let lambda_typ = T_arrowtype [new_name_typ; new_name_typ] in
    T_app (T_exp_basic T_sliceupdate $@ anytype', 
      [list_name n; transform_exp NORMAL e1; transform_exp NORMAL e2; T_lambda ([new_name, new_name_typ], extend_term) $@ lambda_typ])
  (* End logic for update *)
  | [{it = IdxP (_, e); _}] -> 
    let lambda_typ = T_arrowtype [new_name_typ; end_term.typ] in
    T_app (T_exp_basic T_listupdate $@ anytype', [list_name n; transform_exp NORMAL e; T_lambda (["_", new_name_typ], end_term) $@ lambda_typ])
  | [{it = DotP (_, a); _}] -> 
    T_record_update (list_name n, ([], transform_atom a), end_term)
  | [{it = SliceP (_, e1, e2); _}] -> 
    T_app (T_exp_basic T_sliceupdate $@ anytype',
      [list_name n; transform_exp NORMAL e1; transform_exp NORMAL e2; end_term])
  (* Middle logic *)
  | {it = IdxP (_, e); note; _} :: ps -> 
    let new_typ = transform_type' NORMAL note in
    let path_term = transform_path' ps new_typ at (n + 1) None is_extend end_term $@ new_typ in
    let new_name = var_prefix ^ string_of_int (n + 1) in 
    let lambda_typ = T_arrowtype [new_name_typ; new_typ] in
    T_app (T_exp_basic T_listupdate $@ anytype', 
      [list_name n; transform_exp NORMAL e; T_lambda ([new_name, new_name_typ], path_term) $@ lambda_typ])
  | {it = DotP (_, a); note; _} :: ps -> 
    let new_typ = transform_type' NORMAL note in
    let (dot_paths, ps') = list_split is_dot ps in 
    let projection_term = List.fold_right (fun p acc -> 
      match p.it with
      | DotP (_, a') -> 
        T_dotapp (([], transform_atom a'), acc) $@ transform_type' NORMAL p.note
      | _ -> error at "Should be a record access" (* Should not happen *)
    ) dot_paths (list_name n) in
    let new_term = T_dotapp (([], transform_atom a), projection_term) $@ new_typ in
    let path_term = transform_path' ps' new_typ at n (Some new_term) is_extend end_term $@ new_typ in
    T_record_update (projection_term, ([], transform_atom a), path_term)
  | ({it = SliceP (_, _e1, _e2); _} as p) :: _ps ->
    (* TODO - this is not entirely correct. Still unsure how to implement this as a term *)
    (* let new_typ = transform_type' NORMAL note in
    let path_term = transform_path' ps new_typ at (n + 1) None is_extend end_term $@ transform_type' NORMAL note in
    let new_name = var_prefix ^ string_of_int (n + 1) in
    let lambda_typ = T_arrowtype [new_name_typ; new_typ] in
    T_app (T_exp_basic T_sliceupdate $@ anytype',
      [list_name n; transform_exp NORMAL e1; transform_exp NORMAL e2; T_lambda ([(new_name, new_name_typ)], path_term) $@ lambda_typ]) *)
    T_unsupported (Il.Print.string_of_path p);
  (* Catch all error if we encounter empty list or RootP *)
  | _ -> error at "Paths should not be empty"

(* Premises *)
let rec transform_premise (is_rel_prem : bool) (p : prem) =
  match p.it with
  | IfPr exp -> 
    let typ = T_type_basic (if is_rel_prem then T_prop else T_bool) in
    let exp_type = if is_rel_prem then RELATION else NORMAL in 
    P_if ((transform_exp exp_type exp).it $@ typ)
  | ElsePr -> P_else
  | LetPr (exp1, exp2, _) -> 
    let eqtyp = T_arrowtype [transform_type' NORMAL exp1.note; transform_type' NORMAL exp2.note; T_type_basic T_bool] in
    P_if (T_app_infix (T_exp_basic T_eq $@ eqtyp, transform_exp NORMAL exp1, transform_exp NORMAL exp2) $@ T_type_basic T_bool)
  | IterPr (p', (iter, [(id, e)])) ->
    P_list_forall (transform_iter iter, transform_premise is_rel_prem p', (transform_var_id id, transform_type' NORMAL e.note))
  | IterPr (p', (iter, [(id, e); (id2, e2)])) ->
    let id_typ = transform_type' NORMAL e.note in
    let id_typ2 = transform_type' NORMAL e2.note in 
    P_list_forall2 (transform_iter iter, transform_premise is_rel_prem p', (transform_var_id id, id_typ), (transform_var_id id2, id_typ2))
  | IterPr _ -> P_unsupported (string_of_prem p) (* TODO could potentially extend this further if necessary *)
  | RulePr (id, _mixop, exp) -> P_rule (transform_user_def_id id, transform_tuple_exp (transform_exp NORMAL) exp)
  | NegPr p' -> P_neg (transform_premise is_rel_prem p')

let transform_deftyp (id : id) (binds : bind list) (deftyp : deftyp) =
  match deftyp.it with
  | AliasT typ -> TypeAliasD (transform_user_def_id id, List.map transform_bind binds, transform_type NORMAL typ)
  | StructT typfields -> RecordD (transform_user_def_id id, List.map transform_bind binds, List.map (fun (a, (_, t, _), _) -> 
    (([], transform_atom a), transform_type' NORMAL t)) typfields)
  | VariantT typcases -> InductiveD (transform_user_def_id id, List.map transform_bind binds, List.map (fun (m, (_, t, _), _) ->
      (([], transform_mixop id.it m), transform_typ_args NORMAL t)) typcases)

let transform_rule (id : id) (r : rule) =
  match r.it with
  | RuleD (rule_id, binds, _mixop, exp, premises) -> 
    ((transform_rule_id rule_id id, List.map transform_bind binds), 
    List.map (transform_premise true) premises, transform_tuple_exp (transform_exp NORMAL) exp)

let transform_clause (fb : function_body option) (c : clause) =
  match c.it, fb with
  | DefD (_binds, args, exp, _prems), None -> (List.map (transform_arg MATCH) args, F_term (transform_exp NORMAL exp))
  | DefD (_binds, args, _, _prems), Some fb -> (List.map (transform_arg MATCH) args, fb)

let transform_inst (_id : id) (i : inst) =
  match i.it with
  | InstD (_binds, args, deftyp) -> 
    match deftyp.it with
    | AliasT typ -> (List.map (transform_arg MATCH) args, transform_type NORMAL typ)
    | _ -> error i.at "Family of variant or records should not exist" (* This should never occur *)

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
          | e :: es -> F_if_else (transform_exp NORMAL (bigAndExp e es), acc_term, otherwise)
        )
      | {it = IfPr exp; _} :: ps -> go (exp :: acc_bool) acc_term otherwise ps
      | {it = LetPr (exp1, exp2, _); _} :: ps -> go acc_bool (F_let (transform_exp NORMAL exp1, transform_exp NORMAL exp2, acc_term)) otherwise ps
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
          transform_clause (Some (encode_prems (F_term (transform_exp NORMAL exp)) F_default (List.rev prems))) clause 
        | {it = DefD(_, _, exp', _); _} :: rev_tail -> 
          let starting_fb = F_term (transform_exp NORMAL exp') in
          let fb = List.fold_left (fun acc clause' -> match clause'.it with
            | DefD(_, _, exp'', prems'') -> encode_prems (F_term (transform_exp NORMAL exp'')) acc (List.rev prems'') 
          ) starting_fb rev_tail in 
          transform_clause (Some fb) clause
      ) :: rearrange_clauses rest
  in
  
  List.map (fun clause -> match clause.it with 
    | DefD(binds, args, exp, prems) -> DefD(binds, args, exp, modify_let_prems (free_list free_arg args) prems) $ clause.at
  ) clauses 
  |> rearrange_clauses

let create_well_formed_function id params inst at =
  let get_typ_from_arg_args_ids (typ : typ) = 
    match typ.it with
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
    let clauses = List.filter_map (fun (m, (binds, typ, prems), _) -> 
      if prems = [] then None else 
      let case_typs = Preprocess.get_case_typs typ in   
      let new_var_exps = List.mapi (fun _idx (e, _t) -> e) case_typs in 
      let new_tup = TupE (new_var_exps) $$ no_region % (TupT case_typs $ no_region) in
      let new_case_exp = CaseE(m, new_tup) $$ no_region % user_typ in
      let new_arg = ExpA new_case_exp $ no_region in 
      let new_args = List.map Preprocess.make_arg params @ [new_arg] in
      let free_vars = (free_list free_exp (get_typ_from_arg_args_ids typ)).varid in
      let filtered_binds = List.filter (fun b -> match b.it with
        | ExpB (id', _) -> not (Set.mem id'.it free_vars) 
        | _ -> false
      ) binds in
      Some (List.map (transform_arg MATCH) new_args, F_premises (List.map transform_bind filtered_binds, List.map (transform_premise true) prems))
    ) typcases in
    let new_arg = List.init (List.length new_params) (fun _ -> T_ident "_" $@ transform_type' NORMAL user_typ) in
    let extra_clause = if (List.length clauses <> List.length typcases) 
      then [(new_arg, F_term (T_exp_basic (T_bool true) $@ T_type_basic T_bool))] 
      else [] 
    in
    Some (DefinitionD (wf_prefix ^ id.it, List.map transform_param new_params, T_type_basic T_prop, clauses @ extra_clause) $ at)
  | _ -> None

let _has_prems clause = 
  match clause.it with
  | DefD (_, _, _, prems) -> prems <> []

let get_inductive_case_prems deftyp = 
  match deftyp.it with
    | VariantT typcases -> List.map (fun (_, (_, _, prems), _) -> List.map (transform_premise true) prems) typcases 
    | StructT typfields -> List.map (fun (_, (_, _, prems), _) -> List.map (transform_premise true) prems) typfields
    | _ -> []

let rec transform_def (partial_map : string StringMap.t ref) (wf_map : ((premise list) list) StringMap.t ref) (def : def) : mil_def list =
  (match def.it with
  | TypD (id, params, [({it = InstD (binds, _, deftyp);_} as inst)]) 
      when Tfamily.check_normal_type_creation inst -> 
    let wf_func = create_well_formed_function id params inst def.at in
    if Option.is_some wf_func then 
      wf_map := StringMap.add id.it (get_inductive_case_prems deftyp) !wf_map;
    [transform_deftyp id binds deftyp]
  | TypD (id, params, insts) -> 
    let bs = List.map transform_param params in 
    let extra_clause = if (StringMap.mem id.it !partial_map) 
      then [(List.map (fun (_, t) -> T_ident "_" $@ t) bs, T_default $@ anytype')]
      else []
    in
    [InductiveFamilyD (transform_user_def_id id, bs, 
    List.map (transform_inst id) insts @ extra_clause)]
  | RelD (id, _, typ, rules) -> 
    [InductiveRelationD (transform_user_def_id id, transform_tuple_to_relation_args NORMAL typ, List.map (transform_rule id) rules)]
  | DecD (id, params, typ, clauses) ->
    (match params, clauses with
      | _, [] -> 
        (* No implementation - resorts to being an axiom *)
        [AxiomD (transform_fun_id id, List.map transform_param params, transform_type' NORMAL typ)]
      | [], [clause] ->
        (* With one clause and no params - this is essentially a global variable *)
        [GlobalDeclarationD (transform_fun_id id, transform_type' NORMAL typ, transform_clause None clause)]
      (* | _ -> *)
      | _, clauses when List.exists _has_prems clauses -> 
        (* HACK - Need to deal with premises in the future. *)
        [AxiomD (transform_fun_id id, List.map transform_param params, transform_type' NORMAL typ)]
      | _ -> 
        (* Normal function *)
        let bs = List.map transform_param params in
        let rt = transform_type' NORMAL typ in
        let has_partial_typ_fam = List.exists (fun p -> match p.it with
          | ExpP (id, _) | TypP id | DefP (id, _, _) | GramP (id, _) -> StringMap.mem id.it !partial_map
        ) params in 
        let extra_clause = if has_partial_typ_fam 
          then [(List.map (fun (_, t) -> T_ident "_" $@ t) bs, F_term (T_default $@ rt))]
          else []
        in
        [DefinitionD (transform_fun_id id, bs, transform_type' NORMAL typ, List.map (transform_clause None) clauses @ extra_clause)]
    )
  | RecD defs -> [MutualRecD (List.concat_map (transform_def partial_map wf_map) defs)]
  | HintD _ | GramD _ -> [UnsupportedD (string_of_def def)]
  ) |> List.map (fun d -> d $ def.at)

(* Making prefix map *)

let string_of_prefix = function
  | {it = El.Ast.TextE s; _} -> s
  | {at; _} -> error at "malformed prefix hint"

let register_prefix (map : string StringMap.t ref) (id : id) (exp : El.Ast.exp) =
  map := StringMap.add (transform_user_def_id id) (string_of_prefix exp) !map

let has_prefix_hint (hint : hint) = hint.hintid.it = "prefix"

let create_prefix_map_inst (map : string StringMap.t ref) (id : id) (i : inst) =
  match i.it with
  | InstD (_binds, _args, deftyp) -> (match deftyp.it with 
    | AliasT _ -> ()
    | StructT typfields -> List.iter (fun (a, _, hints) ->
      (match (List.find_opt has_prefix_hint hints) with
        | Some h -> 
          let combined_id = atom_string_combine a id.it in
          register_prefix map (combined_id $ id.at) h.hintexp
        | _ -> ()
      )
    ) typfields
    | VariantT typcases -> List.iter (fun (m, _, hints) ->
      (match (List.find_opt has_prefix_hint hints) with
      | Some h -> 
        let combined_id = mixop_string_combine m id.it in
        register_prefix map (combined_id $ id.at) h.hintexp
      | _ -> ()
      )
    ) typcases
  )

let create_prefix_map_def (map : string StringMap.t ref) (d : def) = 
  match d.it with
    | HintD {it = TypH (id, hints); _}
    | HintD {it = RelH (id, hints); _} ->
      (match (List.find_opt has_prefix_hint hints) with
      | Some h -> register_prefix map id h.hintexp
      | _ -> ()
      ) 
    | TypD (id, _, insts) -> List.iter (create_prefix_map_inst map id) insts
    | _ -> ()

let create_prefix_map (il : script) = 
  let map = ref StringMap.empty in
  List.iter (create_prefix_map_def map) il;
  !map

(* Making partial type family map *)

let register_partial_type (map : string StringMap.t ref) (id :id) =
  map := StringMap.add id.it id.it !map

let has_partialtype_hint (hint : hint) = hint.hintid.it = "partial"

let register_partial_type_hint_def (map : string StringMap.t ref) (d : def) = 
  match d.it with
  | HintD {it = TypH (id, hints); _} ->
    (match (List.find_opt has_partialtype_hint hints) with
    | Some _ -> register_partial_type map id
    | _ -> ()
    )
  | _ -> ()

(* Main transformation function *)

let is_not_hintdef (d : def) : bool =
  match d.it with
  | HintD _ -> false
  | _ -> true 

let transform (reserved_ids : StringSet.t) (il : script) =
  let preprocessed_il = Preprocess.preprocess il in
  let partial_map = ref StringMap.empty in 
  let prefix_map = create_prefix_map preprocessed_il in 
  let wf_map = ref StringMap.empty in 

  reserved_ids_set := reserved_ids; 
  env_ref := Il.Env.env_of_script preprocessed_il;

  List.iter (register_partial_type_hint_def partial_map) preprocessed_il;
  List.filter is_not_hintdef preprocessed_il |> 
  List.concat_map (transform_def partial_map wf_map) |>
  
  Naming.transform prefix_map |>
  Wf.transform wf_map 