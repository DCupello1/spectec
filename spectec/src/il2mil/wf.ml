open Util.Source
open Mil.Ast
open Mil.Utils
open Mil.Free
open Util

module StringMap = Map.Make(String)
type wf_entry = 
  | NormalType of (premise list) list
  | FamilyType of (term list) list
  | ExtraType

type wf_env = {
  mil_env : Mil.Env.t;
  mutable wf_type_map : wf_entry StringMap.t;
}

let error at msg = Error.error at "MIL Transformation" msg

let wf_pred_prefix = "wf_"

let wf_pred_suffix = "_wf"

let bind_name = "x"

let new_env wf_type_map script = 
{
  mil_env = Mil.Env.env_of_script script;
  wf_type_map = wf_type_map
}

let bind_wf_inductive_map env id =
  if not (StringMap.mem id env.wf_type_map) then 
    env.wf_type_map <- StringMap.add id ExtraType env.wf_type_map

let rec transform_term env t =
  (transform_type env t.it) $@ transform_type env t.typ

and transform_type env t = 
  let t_func = transform_term env in
  let t_func' = transform_type env in
  match t with
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

let rec get_wf_pred env var t = 
  let t' = Mil.Env.reduce_typealias env.mil_env t in
  match t' with
  | T_app ({it = T_ident id; _}, args) when StringMap.mem id env.wf_type_map -> Some (P_rule (wf_pred_prefix ^ id, args @ [var]))
  | T_ident id when StringMap.mem id env.wf_type_map -> Some (P_rule (wf_pred_prefix ^ id, [var]))
  | T_app ({it = T_type_basic T_opt; _}, [t']) ->
    let inner_var = T_ident bind_name $@ t'.it in
    let prem_opt = get_wf_pred env inner_var t'.it in
    Option.map (fun p -> P_list_forall (I_option, p, (bind_name, t'.it), var)) prem_opt
  | T_app ({it = T_type_basic T_list; _}, [t']) ->
    let inner_var = T_ident bind_name $@ t'.it in
    let prem_opt = get_wf_pred env inner_var t'.it in
    Option.map (fun p -> P_list_forall (I_list, p, (bind_name, t'.it), var)) prem_opt
  | _ -> None

let create_well_formed_inductive_predicate env id dep_binders entries at prems =
  let dep_type = T_arrowtype ((List.map (fun (_, t) -> t) dep_binders) @ [anytype']) in 
  let user_typ = T_app (T_ident id $@ dep_type, List.map (fun (typ_id, typ) -> T_ident typ_id $@ typ) dep_binders) in 
  let new_binder = ("x", user_typ) in
  let new_binders = dep_binders @ [new_binder] in 
  let cases = List.map (fun ((case_id, case_binders), (prems)) -> 
    let new_var_typs = List.map (fun (typ_id, typ) -> T_ident typ_id $@ typ) case_binders in 
    let new_case_term = T_caseapp (case_id, new_var_typs) $@ user_typ in
    let dep_vars_terms = List.map (fun (id', typ) -> T_ident id' $@ typ) dep_binders in
    let case_free_vars = (union (free_list free_premise prems) (free_list free_term (new_case_term :: dep_vars_terms))).var |> VarSet.to_list in 
    let extra_prems = List.filter_map (fun (var, t) -> get_wf_pred env (T_ident var $@ t) t) case_binders in
    ((Mil.Print.string_of_prefixed_ident case_id ^ wf_pred_suffix, case_free_vars), extra_prems @ List.map (transform_premise env) prems, dep_vars_terms @ [new_case_term])
  ) (List.combine entries prems) in
  let has_no_prems = List.for_all (fun (_, prems, _) -> prems = []) cases in
  let relation = InductiveRelationD (wf_pred_prefix ^ id, List.map snd (transform_binders env new_binders), cases) $ at in 
  
  if has_no_prems then None else
  (bind_wf_inductive_map env id; Some relation)
  
let create_well_formed_family_predicate env id dep_binders entries at terms_list = 
  let dep_type = T_arrowtype ((List.map (fun (_, t) -> t) dep_binders) @ [anytype']) in 
  let user_typ = T_app (T_ident id $@ dep_type, List.map (fun (typ_id, typ) -> T_ident typ_id $@ typ) dep_binders) in 
  let new_binder = ("x", user_typ) in
  let new_binders = dep_binders @ [new_binder] in
  let cases = List.map (fun ((case_id, (t_id, typ)), terms) ->
    let case_var = T_ident t_id $@ typ in
    let new_case_term = T_caseapp (([], case_id), [case_var]) $@ user_typ in
    let case_free_vars = (diff (free_list free_term (new_case_term :: terms)) (bound_binders dep_binders)).var |> VarSet.to_list in 
    let extra_prems = List.filter_map (fun (var, t) -> get_wf_pred env (T_ident var $@ t) t) [(t_id, typ)] in
    ((case_id ^ wf_pred_suffix, case_free_vars), extra_prems, terms @ [new_case_term])
  ) (List.combine entries terms_list) in
  InductiveRelationD (wf_pred_prefix ^ id, List.map snd (transform_binders env new_binders), cases) $ at

let create_well_formed_record_predicate env id dep_binders (entries : record_entry list) at = 
  let dep_type = T_arrowtype ((List.map (fun (_, t) -> t) dep_binders) @ [anytype']) in 
  let user_typ = T_app (T_ident id $@ dep_type, List.map (fun (typ_id, typ) -> T_ident typ_id $@ typ) dep_binders) in 
  let new_binder = (bind_name, user_typ) in
  let new_binders = dep_binders @ [new_binder] in 
  let new_term = T_ident bind_name $@ user_typ in
  let extra_prems = List.filter_map (fun (p_id, typ) -> get_wf_pred env (T_dotapp (p_id, new_term) $@ typ) typ) entries in
  let case = ((id ^ wf_pred_suffix, new_binders), extra_prems, [new_term]) in
  let relation = InductiveRelationD (wf_pred_prefix ^ id, List.map snd (transform_binders env new_binders), [case]) $ at in 
  
  if extra_prems = [] then None else 
  (bind_wf_inductive_map env id; Some relation)
   
let rec transform_def env (d : mil_def) =
  match d.it with
  | TypeAliasD (id, bs, t) -> (TypeAliasD (id, transform_binders env bs, transform_type env t) $ d.at, [])
  | RecordD (id, bs, record_entries) -> 
    let record_def = RecordD (id, transform_binders env bs, List.map (fun (id', t) -> (id', transform_type env t)) record_entries) $ d.at in 
    (match (StringMap.find_opt id env.wf_type_map) with
    | None ->
      (record_def, Option.to_list (create_well_formed_record_predicate env id bs record_entries d.at))
    | Some (NormalType _prems) -> (record_def, Option.to_list (create_well_formed_record_predicate env id bs record_entries d.at))
    | _ -> error d.at "Expected a single type, found a type family instead"
    )
  | InductiveD (id, bs, entries) -> 
    let inductive_def = InductiveD (id, transform_binders env bs, List.map (fun (id', bs) -> (id', transform_binders env bs)) entries) $ d.at in 
    let wf_pred_func = create_well_formed_inductive_predicate env id bs entries d.at in
    (match (StringMap.find_opt id env.wf_type_map) with
    | None ->
      let prems = List.init (List.length entries) (fun _ -> []) in
      (inductive_def, Option.to_list (wf_pred_func prems))
    | Some (NormalType prems) -> (inductive_def, Option.to_list (wf_pred_func prems))
    | _ -> error d.at "Expected a single type, found a type family instead"
    )
  | MutualRecD defs -> 
    let (defs', wf_defs) = List.split (List.map (transform_def env) defs) in 
    (MutualRecD defs' $ d.at, List.concat wf_defs)
  | DefinitionD (id, bs, rt, clauses) -> (DefinitionD (id, transform_binders env bs, transform_type env rt,
    List.map (fun (ts, fb) -> (List.map (transform_term env) ts, transform_fb env fb)) clauses) $ d.at, [])
  | GlobalDeclarationD (id, rt, (ts, fb)) -> (GlobalDeclarationD (id, transform_type env rt, (List.map (transform_term env) ts, transform_fb env fb)) $ d.at, [])
  | InductiveRelationD (id, types, entries) -> (InductiveRelationD (id, List.map (transform_type env) types, 
    List.map (fun ((id, bs), prems, terms) -> 
      ((id, transform_binders env bs), 
        List.map (transform_premise env) prems,
        List.map (transform_term env) terms)
    ) entries) $ d.at, [])
  | AxiomD (id, bs, rt) -> (AxiomD (id, transform_binders env bs, transform_type env rt) $ d.at, [])
  | InductiveFamilyD (id, bs, entries) -> 
    let family_def = InductiveFamilyD (id, transform_binders env bs, List.map (fun (case_id, (t_id, typ)) -> 
      (case_id, (t_id, transform_type env typ))) entries) in
    let wf_pred_func = create_well_formed_family_predicate env id bs entries d.at in
    (match (StringMap.find_opt id env.wf_type_map) with
    | Some (FamilyType terms) -> (family_def $ d.at, [wf_pred_func terms])
    | _ -> error d.at "Expected to find a family type, found none"
    )
  | CoercionD (id1, id2, id3) -> (CoercionD (id1, id2, id3) $ d.at, []) 
  | LemmaD (id, binders, prems) -> (LemmaD (id, transform_binders env binders, List.map (transform_premise env) prems) $ d.at, [])
  | UnsupportedD str -> (UnsupportedD str $ d.at, [])
  
  
let transform wf_type_map mil = 
  let env = new_env !wf_type_map mil in
  List.concat_map (fun d -> 
    let (d', wf_defs) = transform_def env d in
    d' :: wf_defs
  ) mil
