open Util.Source
open Mil.Ast
open Mil.Utils
open Util

module StringMap = Map.Make(String)

type wf_env = {
  mil_env : Mil.Env.t;
  mutable wf_map : mil_def StringMap.t
}

let error at msg = Error.error at "MIL Transformation" msg

let wf_prefix = "good_"

let new_env wf_map script = 
{
  mil_env = Mil.Env.env_of_script script;
  wf_map = wf_map
}

let rec transform_term env t =
  (transform_term' env t.it) $@ transform_term' env t.typ

and transform_term' env t = 
  let t_func = transform_term env in
  let t_func' = transform_term' env in
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
  List.map (fun (id, t) -> (id, transform_term' env t)) bs

let rec transform_premise env p = 
  match p with
  | P_if t -> P_if (transform_term env t)
  | P_neg p' -> P_neg (transform_premise env p')
  | P_rule (id, terms) -> P_rule (id, List.map (transform_term env) terms)
  | P_else -> P_else
  | P_list_forall (iter, p', (id, t)) -> P_list_forall (iter, transform_premise env p', (id, transform_term' env t))
  | P_list_forall2 (iter, p', (id1, t1), (id2, t2)) ->
    P_list_forall2 (iter, transform_premise env p', (id1, transform_term' env t1), (id2, transform_term' env t2))
  | p' -> p'

let rec transform_fb env f =
  match f with
  | F_term t -> F_term (transform_term env t)
  | F_premises (bs, ps) -> 
    F_premises (List.map (fun (id, t) -> (id, transform_term' env t)) bs, 
    List.map (transform_premise env) ps)
  | F_if_else (t, f1, f2) -> F_if_else (transform_term env t, transform_fb env f1, transform_fb env f2)
  | F_let (t1, t2, fb) -> F_let (transform_term env t1, transform_term env t2, transform_fb env fb)
  | F_match t -> F_match (transform_term env t)
  | F_default -> F_default

let get_wf_id (wf_pred : mil_def) =
  match wf_pred.it with 
  | DefinitionD (id, _, _, _) -> id
  | _ -> error wf_pred.at "Well formed predicate should be a function definition"

let create_well_formed_type type_id binders wf_predicate at =
  let wf_id = get_wf_id wf_predicate in
  let wf_type_id = wf_prefix ^ type_id in
  let field_type_id = ([], wf_type_id ^ "_KEY") in 
  let field_pred_id = ([], wf_type_id ^ "_PRED") in
  let typ = T_app (T_ident type_id $@ anytype', List.map (fun b -> typ_to_term (snd b)) binders) in
  let pred_field = T_app (T_ident wf_id $@ anytype', List.map (fun b -> typ_to_term (snd b)) binders @ [T_ident (snd field_type_id) $@ anytype']) in
  RecordD (wf_type_id, binders, [(field_type_id, typ); (field_pred_id, pred_field)]) $ at
  
let rec transform_def env (d : mil_def) =
  match d.it with
  | TypeAliasD (id, bs, t) -> [TypeAliasD (id, transform_binders env bs, transform_term env t) $ d.at]
  | RecordD (id, bs, record_entries) -> [RecordD (id, transform_binders env bs, List.map (fun (id', t) -> (id', transform_term' env t)) record_entries) $ d.at]
  | InductiveD (id, bs, entries) -> 
    let inductive_def = InductiveD (id, transform_binders env bs, List.map (fun (id', bs) -> (id', transform_binders env bs)) entries) in 
    (match (StringMap.find_opt id env.wf_map) with
    | None -> [inductive_def $ d.at]
    | Some wf_pred -> [inductive_def $ d.at; wf_pred]
    )
  | MutualRecD defs -> [MutualRecD (List.concat_map (transform_def env) defs) $ d.at]
  | DefinitionD (id, bs, rt, clauses) -> [DefinitionD (id, transform_binders env bs, transform_term' env rt,
    List.map (fun (ts, fb) -> (List.map (transform_term env) ts, transform_fb env fb)) clauses) $ d.at]
  | GlobalDeclarationD (id, rt, (ts, fb)) -> [GlobalDeclarationD (id, transform_term' env rt, (List.map (transform_term env) ts, transform_fb env fb)) $ d.at]
  | InductiveRelationD (id, types, entries) -> [InductiveRelationD (id, List.map (transform_term env) types, 
    List.map (fun ((id, bs), prems, terms) -> 
      ((id, transform_binders env bs), 
        List.map (transform_premise env) prems, 
        List.map (transform_term env) terms)
    ) entries) $ d.at]
  | AxiomD (id, bs, rt) -> [AxiomD (id, transform_binders env bs, transform_term' env rt) $ d.at]
  | InductiveFamilyD (id, bs, entries) -> [InductiveFamilyD (id, transform_binders env bs, 
    List.map (fun (match_terms, term) -> (List.map (transform_term env) match_terms, transform_term env term)) entries) $ d.at]
  | CoercionD (id1, id2, id3) -> [CoercionD (id1, id2, id3) $ d.at]
  | LemmaD (id, binders, prems) -> [LemmaD (id, transform_binders env binders, List.map (transform_premise env) prems) $ d.at]
  | UnsupportedD str -> [UnsupportedD str $ d.at]
  
  
let transform wf_map mil = 
  let env = new_env !wf_map mil in
  List.concat_map (transform_def env) mil
