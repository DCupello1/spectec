open Util.Source
open Mil.Ast
open Mil.Utils
open Mil.Free
open Util

module StringMap = Map.Make(String)

type wf_env = {
  mil_env : Mil.Env.t;
  mutable wf_map : (premise list) list StringMap.t
}

let error at msg = Error.error at "MIL Transformation" msg

let wf_pred_prefix = "wf_"

let wf_pred_suffix = "_wf"

let new_env wf_map script = 
{
  mil_env = Mil.Env.env_of_script script;
  wf_map = wf_map
}

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
  | P_list_forall (iter, p', (id, t)) -> P_list_forall (iter, transform_premise env p', (id, transform_type env t))
  | P_list_forall2 (iter, p', (id1, t1), (id2, t2)) ->
    P_list_forall2 (iter, transform_premise env p', (id1, transform_type env t1), (id2, transform_type env t2))
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

let create_well_formed_predicate env id dep_binders (entries : inductive_type_entry list) prems at =
  let dep_type = T_arrowtype ((List.map (fun (_, t) -> t) dep_binders) @ [anytype']) in 
  let user_typ = T_app (T_ident id $@ dep_type, List.map (fun (typ_id, typ) -> T_ident typ_id $@ typ) dep_binders) in 
  let new_binder = ("x", user_typ) in
  let new_binders = dep_binders @ [new_binder] in 
  let cases = List.map (fun ((case_id, case_binders), (prems)) -> 
    let prefixes, base_id = case_id in
    let new_var_typs = List.map (fun (typ_id, typ) -> T_ident typ_id $@ typ) case_binders in 
    let new_case_term = T_caseapp (case_id, new_var_typs) $@ user_typ in
    let dep_vars_terms = List.map (fun (id', typ) -> T_ident id' $@ typ) dep_binders in
    let case_free_vars = (union (free_list free_premise prems) (free_list free_term (new_case_term :: dep_vars_terms))).var |> VarSet.to_list in 
    ((String.concat "" prefixes ^ base_id ^ wf_pred_suffix, case_free_vars), List.map (transform_premise env) prems, dep_vars_terms @ [new_case_term])
  ) (List.combine entries prems) in
  InductiveRelationD (wf_pred_prefix ^ id, List.map snd (transform_binders env new_binders), cases) $ at
  
let rec transform_def env (d : mil_def) =
  match d.it with
  | TypeAliasD (id, bs, t) -> (TypeAliasD (id, transform_binders env bs, transform_type env t) $ d.at, [])
  | RecordD (id, bs, record_entries) -> (RecordD (id, transform_binders env bs, List.map (fun (id', t) -> (id', transform_type env t)) record_entries) $ d.at, [])
  | InductiveD (id, bs, entries) -> 
    let inductive_def = InductiveD (id, transform_binders env bs, List.map (fun (id', bs) -> (id', transform_binders env bs)) entries) in 
    (match (StringMap.find_opt id env.wf_map) with
    | None -> (inductive_def $ d.at, [])
    | Some (prems) -> (inductive_def $ d.at, [create_well_formed_predicate env id bs entries prems d.at])
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
  | InductiveFamilyD (id, bs, entries) -> (InductiveFamilyD (id, transform_binders env bs, 
    List.map (fun (match_terms, term) -> (List.map (transform_term env) match_terms, transform_term env term)) entries) $ d.at, [])
  | CoercionD (id1, id2, id3) -> (CoercionD (id1, id2, id3) $ d.at, [])
  | LemmaD (id, binders, prems) -> (LemmaD (id, transform_binders env binders, List.map (transform_premise env) prems) $ d.at, [])
  | UnsupportedD str -> (UnsupportedD str $ d.at, [])
  
  
let transform wf_map mil = 
  let env = new_env !wf_map mil in
  List.concat_map (fun d -> 
    let (d', wf_defs) = transform_def env d in
    d' :: wf_defs
  ) mil
