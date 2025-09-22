open Util.Source
open Mil.Ast

let is_dep_type env t = 
  match t with
  | T_app ({it = T_ident id; _}, args) -> args <> [] && Mil.Env.mem_typ env id
  | _ -> false

let rec transform_term env t =
  (transform_type env t.it) $@ transform_type env t.typ

and transform_type env t = 
  let t_func = transform_term env in
  let t_func' = transform_type env in
  match t with
  | T_list terms -> T_list (List.map t_func terms)
  | T_record_update (t1, p_id, t2) -> T_record_update (t_func t1, p_id, t_func t2)
  | T_record_fields fields -> T_record_fields (List.map (fun (p_id, t') -> (p_id, t_func t')) fields)
  | T_lambda (bs, t') -> T_lambda (transform_binders env bs, t_func t')
  | T_caseapp (p_id, terms) -> T_caseapp (p_id, List.map t_func terms)
  | T_dotapp (p_id, term) -> T_dotapp (p_id, t_func term)
  | T_app ({it = T_ident id; typ = T_arrowtype ts}, args) when args <> [] && Mil.Env.mem_typ env id ->
    let args_filtered = List.filter (fun t -> t.typ = T_type_basic T_anytype) args in
    List.iter (fun t -> print_endline (Mil.Print.string_of_term (transform_term env t))) args_filtered;
    let typ_filtered = T_arrowtype (List.filter (fun t -> t = T_type_basic T_anytype) ts) in 
    if args_filtered = [] then T_ident id else T_app (T_ident id $@ typ_filtered, args_filtered)
  | T_app (t', terms) -> 
    T_app (t_func t', List.map t_func terms)
  | T_app_infix (t1, t2, t3) -> T_app_infix (t_func t1, t_func t2, t_func t3)
  | T_tuple terms -> T_tuple (List.map t_func terms)
  | T_tupletype terms -> T_tupletype (List.map t_func' terms)
  | T_arrowtype terms -> T_arrowtype (List.map t_func' terms)
  | T_cast (t', typ1, typ2) -> T_cast (t_func t', t_func' typ1, t_func' typ2)
  | t' -> t'

and transform_binders env bs =
  List.map (fun (id, t) -> (id, transform_type env t)) bs

and transform_dep_binders env bs = 
  List.filter (fun (_, t) -> t = T_type_basic T_anytype) bs |>
  transform_binders env

let rec transform_premise env p = 
  match p with
  | P_if t -> P_if (transform_term env t)
  | P_neg p' -> P_neg (transform_premise env p')
  | P_rule (id, terms) -> P_rule (id, List.map (transform_term env) terms)
  | P_else -> P_else
  | P_list_forall (iter, p', (v, v_t), v_iter_term) -> P_list_forall (iter, transform_premise env p', (v, transform_type env v_t), transform_term env v_iter_term)
  | P_list_forall2 (iter, p', (v, v_t), (s, s_t), v_iter_term, s_iter_term) ->
    P_list_forall2 (iter, transform_premise env p', (v, transform_type env v_t), (s, transform_type env s_t), transform_term env v_iter_term, transform_term env s_iter_term)
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
  | TypeAliasD (id, bs, t) -> TypeAliasD (id, transform_dep_binders env bs, transform_type env t) 
  | RecordD (id, bs, record_entries) -> RecordD (id, transform_dep_binders env bs, List.map (fun (id', t) -> (id', transform_type env t)) record_entries)
  | InductiveD (id, bs, entries) -> InductiveD (id, transform_dep_binders env bs,
    List.map (fun (id', bs) -> (id', transform_binders env bs)) entries)
  | MutualRecD defs -> MutualRecD (List.map (transform_def env) defs)
  | DefinitionD (id, bs, rt, clauses) -> DefinitionD (id, transform_binders env bs, transform_type env rt,
    List.map (fun (ts, fb) -> (List.map (transform_term env) ts, transform_fb env fb)) clauses)
  | GlobalDeclarationD (id, rt, (ts, fb)) -> GlobalDeclarationD (id, transform_type env rt, (List.map (transform_term env) ts, transform_fb env fb))
  | InductiveRelationD (id, types, entries) -> 
    InductiveRelationD (id, List.map (transform_type env) types, 
    List.map (fun ((id, bs), prems, terms) -> 
      ((id, transform_binders env bs), 
        List.map (transform_premise env) prems, 
        List.map (transform_term env) terms)
    ) entries)
  | AxiomD (id, bs, rt) -> AxiomD (id, transform_binders env bs, transform_type env rt)
  | InductiveFamilyD (id, bs, entries) -> InductiveFamilyD (id, transform_dep_binders env bs, 
    List.map (fun (id, (t_id, typ)) -> (id, (t_id, transform_type env typ))) entries)
  | CoercionD (id1, typ1, typ2) -> CoercionD (id1, transform_type env typ1, transform_type env typ2)
  | LemmaD (id, binders, prems) -> LemmaD (id, transform_binders env binders, List.map (transform_premise env) prems)
  | UnsupportedD str -> UnsupportedD str
  ) $ d.at

let transform mil = 
  let env = Mil.Env.env_of_script mil in
  List.map (transform_def env) mil
