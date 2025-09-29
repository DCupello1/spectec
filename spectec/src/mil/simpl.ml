open Util.Source
open Ast
open Utils

let match_iter_to_typ i = 
  (match i with
  | I_list -> T_type_basic T_list
  | I_option -> T_type_basic T_opt
  ) $@ anytype'
let rec transform_term env t =
  (transform_type env t.it) $@ transform_type env t.typ

and transform_type env t = 
  let t_func = transform_term env in
  let t_func' = transform_type env in
  match t with
  (* List.map or Option.map of identity function should just return the inputted list *)
  | T_app ({it = T_exp_basic (T_map _); _}, 
    [{it = T_lambda ([(id, _)], {it = T_ident id'; _}); _}; term]) when id = id' -> 
    term.it
  (* List.map or Option.map of a function that only casts should just return the inputted list converted to the new list *)
  | T_app ({it = T_exp_basic (T_map iter); _}, 
    [{it = T_lambda ([(id, _)], {it = T_cast ({it = T_ident id'; _}, t1, t2); _}); _}; term]) when id = id' -> 
    let iter_t1 = T_app (match_iter_to_typ iter, [Utils.typ_to_term t1]) in
    let iter_t2 = T_app (match_iter_to_typ iter, [Utils.typ_to_term t2]) in
    T_cast (term, iter_t1, iter_t2)
  | T_list terms -> T_list (List.map t_func terms)
  | T_record_update (t1, p_id, t2) -> T_record_update (t_func t1, p_id, t_func t2)
  | T_record_fields fields -> T_record_fields (List.map (fun (p_id, t') -> (p_id, t_func t')) fields)
  | T_lambda (ids, t') -> T_lambda (ids, t_func t')
  | T_caseapp (p_id, terms) -> T_caseapp (p_id, List.map t_func terms)
  | T_dotapp (p_id, term) -> T_dotapp (p_id, t_func term)
  | T_app (t', terms) -> T_app (t_func t', List.map t_func terms)
  | T_app_infix (t1, t2, t3) -> T_app_infix (t_func t1, t_func t2, t_func t3)
  | T_tuple terms -> T_tuple (List.map t_func terms)
  | T_tupletype terms -> T_tupletype (List.map t_func' terms)
  | T_arrowtype terms -> T_arrowtype (List.map t_func' terms)
  | T_cast (t', typ1, typ2) when typ1 = typ2 -> (t_func t').it 
  | T_cast (t', typ1, typ2) -> T_cast (t_func t', t_func' typ1, t_func' typ2)
  | t' -> t'

and transform_binders env bs =
  List.map (fun (id, t) -> (id, transform_type env t)) bs

let rec transform_premise env p = 
  match p with
  | P_if t -> P_if (transform_term env t)
  | P_neg p' -> P_neg (transform_premise env p')
  | P_rule (id, terms) -> P_rule (id, List.map (transform_term env) terms)
  | P_else -> P_else
  | P_list_forall (iter, p', (id, t), t') -> P_list_forall (iter, transform_premise env p', (id, transform_type env t), transform_term env t')
  | P_list_forall2 (iter, p', (id1, t1), (id2, t2), t1', t2') ->
    P_list_forall2 (iter, transform_premise env p', 
    (id1, transform_type env t1), (id2, transform_type env t2),
    transform_term env t1', transform_term env t2')
  | p' -> p'

let rec transform_fb env f =
  match f with
  | F_term t -> F_term (transform_term env t)
  | F_premises (bs, ps) -> 
    F_premises (List.map (fun (id, t) -> (id, transform_type env t)) bs, 
    List.map (transform_premise env) ps)
  | F_if_else (t, f1, f2) -> F_if_else (transform_term env t, transform_fb env f1, transform_fb env f2)
  | F_let (t1, t2, fb) -> F_let (transform_term env t1, transform_term env t2, transform_fb env fb)
  | F_match t -> F_match (transform_term env t)
  | F_default -> F_default
  
let rec transform_def env (d: mil_def) =
  (match d.it with
  | TypeAliasD (id, bs, t) -> TypeAliasD (id, transform_binders env bs, transform_type env t) 
  | RecordD (id, bs, record_entries) -> RecordD (id, transform_binders env bs, List.map (fun (id', t) -> (id', transform_type env t)) record_entries)
  | InductiveD (id, bs, entries) -> InductiveD (id, transform_binders env bs,
    List.map (fun (id', bs) -> (id', transform_binders env bs)) entries)
  | MutualRecD defs -> MutualRecD (List.map (transform_def env) defs)
  | DefinitionD (id, bs, rt, clauses) -> DefinitionD (id, transform_binders env bs, transform_type env rt,
    List.map (fun (ts, fb) -> (List.map (transform_term env) ts, transform_fb env fb)) clauses)
  | GlobalDeclarationD (id, rt, (ts, fb)) -> GlobalDeclarationD (id, transform_type env rt, (List.map (transform_term env) ts, transform_fb env fb))
  | InductiveRelationD (id, types, entries) -> InductiveRelationD (id, List.map (transform_type env) types, 
    List.map (fun ((id, bs), prems, terms) -> 
      ((id, transform_binders env bs), 
        List.map (transform_premise env) prems, 
        List.map (transform_term env) terms)
    ) entries)
  | AxiomD (id, bs, rt) -> AxiomD (id, transform_binders env bs, transform_type env rt)
  | InductiveFamilyD (id, bs, entries) -> InductiveFamilyD (id, transform_binders env bs, 
    List.map (fun (case_id, (id', typ)) -> (case_id, (id', transform_type env typ))) entries)
  | CoercionD (id1, id2, id3) -> CoercionD (id1, id2, id3)
  | LemmaD (id, binders, prems) -> LemmaD (id, transform_binders env binders, List.map (transform_premise env) prems)
  | UnsupportedD str -> UnsupportedD str
  ) $ d.at
let transform mil = 
  let env = 0 in
  List.map (transform_def env) mil
