open Il.Ast
open Il.Print
open Il.Free
open Ast
open Util
open Source
open Either


let error at msg = Error.error at "MIL Transformation" msg
let family_type_suffix = "entry"
let coerce_prefix = "coec_"

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

(* Id transformation *)
let transform_id' (s : text) = match s with
  | s -> String.map (function
     | '.' -> '_'
     | '-' -> '_'
     | c -> c
     ) s

let transform_id (id : id) = transform_id' id.it

let transform_iter (iter : iter) =
  if iter = Opt then I_option else I_list

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
    | GramB _  -> assert false (* Avoiding this for now *) 
    
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

let transform_itertyp (it : iter) =
  match it with
    | Opt -> T_type_basic T_opt
    | List | List1 | ListN _ -> T_type_basic T_list

let transform_numtyp (typ : numtyp) = 
  match typ with
    | `NatT -> T_type_basic T_nat
    | `IntT -> T_type_basic T_int
    | `RatT -> T_type_basic T_rat (*T_unsupported "rat"*)
    | `RealT -> T_type_basic T_real (*T_unsupported "real"*)

let rec transform_type (typ : typ) =
  match typ.it with
    | VarT (id, []) -> T_ident [transform_id id]
    | VarT (id, args) -> 
      let get_typ a = match a.it with
        | ExpA exp -> transform_type exp.note
        | TypA typ -> transform_type typ 
        | DefA _ | GramA _ -> assert false (* TODO Extend later *)
      in 
      let var_type = List.fold_right (fun term acc -> T_arrowtype (term, acc)) (List.map get_typ args) (T_type_basic T_anytype) in
      T_app (T_ident [transform_id id], var_type, List.map transform_arg args)
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
    | VarE id -> T_ident [transform_id id]
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
    | TupE exps -> T_match (List.map transform_exp exps) 
    | ProjE (e, n) -> T_app (T_exp_basic T_listlookup, typ,[transform_exp e; T_exp_basic (T_nat (Z.of_int n))])
    | CaseE (mixop, e) ->
      T_app (T_ident [transform_mixop mixop], typ, transform_tuple_exp transform_exp e)
    | UncaseE (_e, _mixop) -> T_unsupported ("UncaseE: " ^ Il.Print.string_of_exp exp) (* Should be removed by preprocessing *)
    | OptE (Some e) -> T_app (T_exp_basic T_some, typ, [transform_exp e])
    | OptE None -> T_exp_basic T_none
    | TheE e -> T_app (T_exp_basic T_invopt, typ, [transform_exp e])
    | StrE expfields -> T_record_fields (List.map (fun (a, e) -> (gen_typ_name exp.note ^ "__" ^ transform_atom a, transform_exp e)) expfields)
    | DotE (e, atom) -> T_app (T_ident [transform_atom atom], typ, [transform_exp e])
    | CompE (exp1, exp2) -> T_app_infix (T_exp_basic T_recordconcat, transform_exp exp1, transform_exp exp2)
    | ListE exps -> T_list (List.map transform_exp exps)
    | LenE e -> T_app (T_exp_basic T_listlength, typ, [transform_exp e])
    | CatE (exp1, exp2) -> T_app_infix (T_exp_basic T_listconcat, transform_exp exp1, transform_exp exp2)
    | IdxE (exp1, exp2) -> T_app (T_exp_basic T_listlookup, typ, [transform_exp exp1; transform_exp exp2])
    | SliceE (exp1, exp2, exp3) -> T_app (T_exp_basic T_slicelookup, typ, [transform_exp exp1; transform_exp exp2; transform_exp exp3])
    | UpdE (exp1, path, exp2) -> T_update (transform_path_start path exp1, transform_exp exp1, transform_exp exp2)
    | ExtE (exp1, path, exp2) -> T_extend (transform_path_start path exp1, transform_exp exp1, transform_exp exp2)
    | CallE (id, args) -> T_app (T_ident [transform_id id], typ, List.map transform_arg args)
    | IterE (exp, (iter, ids)) ->  
        let exp1 = transform_exp exp in
        (match iter, ids, exp.it with
        | (List | List1 | ListN _), [], _ -> T_list [exp1] 
        | Opt, [], _ -> T_app (T_exp_basic T_some, typ, [exp1])
        | (List | List1 | ListN _ | Opt), _, (VarE _ | IterE _) -> exp1 
        | Opt, [(_, _)], OptE (Some e) -> T_app (T_exp_basic T_some, typ, [transform_exp e])
        | (List | List1 | ListN _ | Opt), [(v, _)], _ -> T_app (T_exp_basic (T_map (transform_iter iter)), typ, [T_lambda ([transform_id v], exp1); T_ident [transform_id v]])
        | (List | List1 | ListN _ | Opt), [(v, _); (s, _)], _ -> T_app (T_exp_basic (T_zipwith (transform_iter iter)), typ, [T_lambda ([transform_id v; transform_id s], exp1); T_ident [transform_id v]; T_ident [transform_id s]])
        | _ -> exp1
      ) 
    | SubE (e, _, typ2) -> T_cast (transform_exp e, transform_type typ2)
    | CvtE (e, _, numtyp) -> T_cast (transform_exp e, transform_numtyp numtyp)
    | LiftE _ -> T_unsupported ("LiftE: " ^ string_of_exp exp)
    | MemE _ -> T_unsupported ("MemE: " ^ string_of_exp exp)

and transform_match_exp (exp : exp) =
  let typ = transform_type exp.note in 
  match exp.it with
  (* Specific match exp handling *)
  | CatE (exp1, exp2) -> T_app_infix (T_exp_basic T_listcons, transform_match_exp exp1, transform_match_exp exp2)
  | IterE (exp, _) -> transform_match_exp exp
  | ListE exps -> (match exps with
    | [e] -> transform_match_exp e
    | _ -> transform_exp exp
  )
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
    T_app (T_ident [transform_mixop mixop], typ, transform_tuple_exp transform_match_exp e)
  | OptE (Some e) -> T_app (T_exp_basic T_some, typ, [transform_match_exp e])
  | OptE None -> T_exp_basic T_none
  | TheE e -> T_app (T_exp_basic T_invopt, typ, [transform_match_exp e])
  | StrE expfields -> T_record_fields (List.map (fun (a, e) -> (transform_atom a, transform_match_exp e)) expfields)
  | DotE (e, atom) -> T_app (T_ident [transform_atom atom], typ, [transform_match_exp e])
  | CompE (exp1, exp2) -> T_app_infix (T_exp_basic T_recordconcat, transform_match_exp exp1, transform_match_exp exp2)
  | LenE e -> T_app (T_exp_basic T_listlength, typ, [transform_match_exp e])
  | IdxE (exp1, exp2) -> T_app (T_exp_basic T_listlookup, typ, [transform_match_exp exp1; transform_match_exp exp2])
  | SliceE (exp1, exp2, exp3) -> T_app (T_exp_basic T_slicelookup, typ, [transform_match_exp exp1; transform_match_exp exp2; transform_match_exp exp3])
  | UpdE (exp1, path, exp2) -> T_update (transform_path_start path exp1, transform_match_exp exp1, transform_match_exp exp2)
  | ExtE (exp1, path, exp2) -> T_extend (transform_path_start path exp1, transform_match_exp exp1, transform_match_exp exp2)
  | CallE (id, args) -> T_app (T_ident [transform_id id], typ, List.map transform_arg args)
  | SubE (e, _, typ2) -> T_cast (transform_match_exp e, transform_type typ2)
  | CvtE (e, _, numtyp) -> T_cast (transform_match_exp e, transform_numtyp numtyp)
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
    | DefA id -> T_ident [id.it]
    | GramA _ -> T_unsupported ("Grammar Arg: " ^ string_of_arg arg)

and transform_match_arg (arg : arg) =
  match arg.it with
    | ExpA exp -> transform_match_exp exp
    | TypA _ -> T_ident ["_"]
    | DefA id -> T_ident [id.it]
    | GramA _ -> T_unsupported ("Grammar Arg: " ^ string_of_arg arg)

and transform_bind (bind : bind) =
  match bind.it with
    | ExpB (id, typ) -> (transform_id id, transform_type typ)
    | TypB id -> (transform_id id, T_type_basic T_anytype)
    | DefB _ -> ("", T_unsupported ("Higher order func: " ^ string_of_bind bind))
    | GramB _ -> ("", T_unsupported ("Grammar bind: " ^ string_of_bind bind))

and transform_param (p : param) =
  match p.it with
    | ExpP (id, typ) -> 
      (transform_id id, transform_type typ)
    | TypP id -> transform_id id, T_type_basic T_anytype
    | DefP _ -> ("", T_unsupported ("Higher order func: " ^ string_of_param p))
    | GramP _ -> ("", T_unsupported ("Grammar param: " ^ string_of_param p))

(* PATH Functions *)
and transform_list_path (p : path) = 
  match p.it with   
    | RootP -> []
    | IdxP (p', e') -> (IdxP (p', e') $$ (p.at, p.note)) :: transform_list_path p'
    | SliceP (p', _exp1, _exp2) -> (SliceP (p', _exp1, _exp2) $$ (p.at, p.note)) :: transform_list_path p'
    | DotP (p', a) -> (DotP (p', a) $$ (p.at, p.note)) :: transform_list_path p'

and gen_path_var_id (exp : exp) = 
  match exp.it with
    | VarE id -> Some (transform_id id)
    | _ -> None

(* TODO: Improve this handling for the case of two listlookups in a row *)
and transform_path (paths : path list) (n : int) (name : string option) = 
  let var_prefix = "v_" in
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
    | LetPr (exp1, exp2, _) -> P_if (T_app_infix (T_exp_basic T_eq, transform_exp exp1, transform_exp exp2))
    | IterPr (p, (iter, [(id, _e)])) ->
      P_forall (transform_iter iter, transform_premise p, transform_id id)
    | IterPr (p, (iter, [(id, _e); (id2, _e2)])) when iter != Opt ->
      P_forall2 (transform_iter iter, transform_premise p, transform_id id, transform_id id2)
    | IterPr _ -> assert false (* TODO check if this makes sense *)
    | RulePr (id, _mixop, exp) -> P_rule (transform_id id, transform_tuple_exp transform_exp exp)

let transform_deftyp (id : id) (binds : bind list) (deftyp : deftyp) =
  match deftyp.it with
    | AliasT typ -> TypeAliasD (transform_id id, List.map transform_bind binds, transform_type typ)
    | StructT typfields -> RecordD (transform_id id, List.map (fun (a, (_, t, _), _) -> 
      (transform_atom a, transform_type t)) typfields)
    | VariantT typcases -> InductiveD (transform_id id, List.map transform_bind binds, List.map (fun (m, (_, t, _), _) ->
        (transform_mixop m, transform_typ_args t)) typcases)

let transform_rule (_id : id) (r : rule) = 
  match r.it with
    | RuleD (rule_id, binds, _mixop, exp, premises) -> 
      ((transform_id rule_id, List.map transform_bind binds), 
      List.map transform_premise premises, transform_tuple_exp transform_exp exp)
let transform_clause (fb : function_body option) (c : clause) =
  match c.it, fb with
    | DefD (_binds, args, exp, _prems), None -> (T_match (List.map transform_match_arg args), F_term (transform_exp exp))
    | DefD (_binds, args, _, _prems), Some fb -> (T_match (List.map transform_match_arg args), fb)

let transform_inst (_id : id) (i : inst) =
  match i.it with
    | InstD (_binds, _, deftyp) -> 
      match deftyp.it with
      | AliasT typ -> TypeAliasT (transform_type typ)
      | StructT _ -> error i.at "Family of records should not exist" (* This should never occur *)
      | VariantT typcases -> 
        InductiveT (List.map (fun (m, (case_binds, _, _), _) -> (transform_mixop m, List.map transform_bind case_binds)) typcases)

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

  let rec modify_let_prems free_vars prems = 
    match prems with
      | [] -> []
      | ({it = IfPr {it = CmpE(`EqOp, _, exp1, exp2); _}; at; _} :: ps) 
        when not (List.is_empty (get_ids exp1)) && not (List.exists (fun id -> Set.mem id.it free_vars.varid) (get_ids exp1)) -> 
        (LetPr (exp1, exp2, (free_exp exp1).varid |> Set.elements) $ at) :: modify_let_prems free_vars ps
      | ({it = IfPr {it = CmpE(`EqOp, _, exp1, exp2); _}; at; _} :: ps) 
        when not (List.is_empty (get_ids exp2)) && not (List.exists (fun id -> Set.mem id.it free_vars.varid) (get_ids exp2)) -> 
        (LetPr (exp2, exp1, (free_exp exp2).varid |> Set.elements) $ at) :: modify_let_prems free_vars ps
      | (p :: ps) ->
        p :: modify_let_prems free_vars ps 
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
    
let rec transform_def (d : def) : mil_def =
  (match d.it with
    | TypD (id, _, [{it = InstD (binds, _, deftyp);_}]) -> transform_deftyp id binds deftyp 
    | TypD (id, _, insts) -> InductiveFamilyD (transform_id id, List.map (transform_inst id) insts)
    | RelD (id, _, typ, rules) -> InductiveRelationD (transform_id id, transform_tuple_to_relation_args typ, List.map (transform_rule id) rules)
    | DecD (id, params, typ, clauses) -> 
      (match params,clauses with
        | _, [] -> AxiomD (transform_id id, List.map transform_param params, transform_type typ)
        | [], [clause] -> GlobalDeclarationD (transform_id id, transform_type typ, transform_clause None clause)
        | _ -> 
          DefinitionD (transform_id id, List.map transform_param params, transform_type typ, List.map (transform_clause None) clauses)
      )
    | RecD defs -> MutualRecD (List.map transform_def defs)
    | HintD _ | GramD _ -> UnsupportedD (string_of_def d)
  ) $ d.at

let is_not_hintdef (d : def) : bool =
  match d.it with
    | HintD _ -> false
    | _ -> true 

(* Main transformation function *)
let transform (il : script) : mil_script =
  let preprocessed_il = Preprocess.preprocess il in 
  List.map transform_def (List.filter is_not_hintdef preprocessed_il) 