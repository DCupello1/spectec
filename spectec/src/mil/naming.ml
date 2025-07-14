open Util.Source
open Ast
open Translate


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
    | s when (s = var_prefix ^ "_") -> go fresh_prefix start
    | s when List.mem s ids -> go i start
    | _ -> i

(* NOTE - This only works for function defs binders since the variables are not used later.
  Would need to make a subst for MIL to make this work for all binders *)
let improve_ids_binders at binders = 
  let rec improve_ids_helper ids bs = 
    match bs with
      | [] -> []
      | (b_id, t) :: bs' -> 
        let new_name = generate_var at ids b_id in 
        (new_name, t) :: improve_ids_helper (new_name :: ids) bs'
  in
  improve_ids_helper [] binders

(* Can only be used for user defined types*)

let rec transform_term prefix_map t =
  let t_func = transform_term prefix_map in
  let t_func' = transform_type prefix_map in
  (match t.it with
  (* Specific case and record fields handling *)
  | T_caseapp (id, terms) -> 
    let id' = Print.get_id t.typ in
    let extra_prefix = (match (StringMap.find_opt id' prefix_map) with 
      | Some prefix -> prefix
      | None -> ""
    ) in 
    let combined_id = string_combine id id' in
    (match (StringMap.find_opt combined_id prefix_map) with 
      | Some prefix -> T_caseapp (extra_prefix ^ prefix ^ id, List.map t_func terms) 
      | None -> T_caseapp (extra_prefix ^ id, List.map t_func terms)
    )
  | T_dotapp (id, term) -> 
    let id' = Print.get_id term.typ in
    let extra_prefix = (match (StringMap.find_opt id' prefix_map) with 
      | Some prefix -> prefix
      | None -> ""
    ) in 
    let combined_id = string_combine id id' in
    (match (StringMap.find_opt combined_id prefix_map) with 
      | Some prefix -> T_dotapp (extra_prefix ^ prefix ^ id, t_func term) 
      | None -> T_dotapp (extra_prefix ^ id, t_func term)
    )
  | T_record_fields fields -> 
    let id' = Print.get_id t.typ in 
    let extra_prefix = (match (StringMap.find_opt id' prefix_map) with 
        | Some prefix -> prefix
        | None -> ""
    ) in 
    T_record_fields ( 
    List.map (fun (id, t) -> 
      let combined_id = string_combine id id' in
      let new_id = (match (StringMap.find_opt combined_id prefix_map) with
        | Some prefix -> extra_prefix ^ prefix ^ id
        | None -> extra_prefix ^ id
      ) in  
      (new_id, t_func t)
    ) fields)
  | T_record_update (t1, id, t3) -> 
    let id' = Print.get_id t1.typ in 
    let extra_prefix = (match (StringMap.find_opt id' prefix_map) with 
        | Some prefix -> prefix
        | None -> ""
    ) in 
    let combined_id = string_combine id id' in
    let new_id = (match (StringMap.find_opt combined_id prefix_map) with
      | Some prefix -> extra_prefix ^ prefix ^ id
      | None -> extra_prefix ^ id
    ) in  
    T_record_update (t_func t1, new_id, t_func t3)
  (* Descend *)
  | T_list terms -> T_list (List.map t_func terms)
  | T_lambda (ids, t) -> T_lambda (ids, t_func t)
  | T_app (t, terms) -> T_app (t_func t, List.map t_func terms)
  | T_app_infix (t1, t2, t3) -> T_app_infix (t_func t1, t_func t2, t_func t3)
  | T_tuple terms -> T_tuple (List.map t_func terms)
  | T_tupletype types -> T_tupletype (List.map t_func' types)
  | T_arrowtype types -> T_arrowtype (List.map t_func' types)
  | T_cast (t, typ1, typ2) -> T_cast (t_func t, t_func' typ1, t_func' typ2)
  | t' -> t') $@ t.typ

and transform_type prefix_map t = (transform_term prefix_map (t $@ anytype')).it 

and transform_binders prefix_map (bs : binder list) =
  List.map (fun (id, t) -> (id, transform_type prefix_map t)) bs

let rec transform_premise prefix_map p = 
  match p with
  | P_if t -> P_if (transform_term prefix_map t)
  | P_neg p' -> P_neg (transform_premise prefix_map p')
  | P_rule (id, terms) -> P_rule (id, List.map (transform_term prefix_map) terms)
  | P_else -> P_else
  | P_list_forall (iter, p', (id, t)) -> P_list_forall (iter, transform_premise prefix_map p', (id, transform_type prefix_map t))
  | P_list_forall2 (iter, p', (id1, t1), (id2, t2)) ->
    P_list_forall2 (iter, transform_premise prefix_map p', (id1, transform_type prefix_map t1), (id2, transform_type prefix_map t2))
  | p' -> p'

let rec transform_fb prefix_map f =
  match f with
  | F_term t -> F_term (transform_term prefix_map t)
  | F_premises (bs, ps) -> 
    F_premises (List.map (fun (id, t) -> (id, transform_type prefix_map t)) bs, 
    List.map (transform_premise prefix_map) ps)
  | F_if_else (t, f1, f2) -> F_if_else (transform_term prefix_map t, transform_fb prefix_map f1, transform_fb prefix_map f2)
  | F_let (t1, t2, fb) -> F_let (transform_term prefix_map t1, transform_term prefix_map t2, transform_fb prefix_map fb)
  | F_match t -> F_match (transform_term prefix_map t)
  | F_default -> F_default


  
let rec transform_def prefix_map (d : mil_def) =
  (match d.it with
  | TypeAliasD (id, bs, t) -> TypeAliasD (id, transform_binders prefix_map bs, transform_term prefix_map t) 
  | RecordD (id, record_entries) -> 
    let extra_prefix = (match (StringMap.find_opt id prefix_map) with 
        | Some prefix -> prefix
        | None -> ""
    ) in 
    RecordD (id, List.map (fun (id', t) -> 
      let combined_id = string_combine id' id in
      let new_id = (match (StringMap.find_opt combined_id prefix_map) with
        | Some prefix -> extra_prefix ^ prefix ^ id'
        | None -> extra_prefix ^ id'
      ) in 
      (new_id, transform_term prefix_map t)) record_entries)
  | InductiveD (id, bs, entries) -> 
    let extra_prefix = (match (StringMap.find_opt id prefix_map) with 
        | Some prefix -> prefix
        | None -> ""
    ) in 
    InductiveD (id, transform_binders prefix_map bs,
    List.map (fun (id', bs) -> 
      let combined_id = string_combine id' id in
      let new_id = (match (StringMap.find_opt combined_id prefix_map) with
        | Some prefix -> extra_prefix ^ prefix ^ id'
        | None -> extra_prefix ^ id'
      ) in 
      (new_id, transform_binders prefix_map bs)
    ) entries)
  | MutualRecD defs -> MutualRecD (List.map (transform_def prefix_map) defs)
  | DefinitionD (id, bs, rt, clauses) -> DefinitionD (id, transform_binders prefix_map (improve_ids_binders d.at bs), transform_type prefix_map rt,
    List.map (fun (ts, fb) -> (List.map (transform_term prefix_map) ts, transform_fb prefix_map fb)) clauses)
  | GlobalDeclarationD (id, rt, (ts, fb)) -> GlobalDeclarationD (id, transform_type prefix_map rt, (List.map (transform_term prefix_map) ts, transform_fb prefix_map fb))
  | InductiveRelationD (id, types, entries) -> 
    let extra_prefix = (match (StringMap.find_opt id prefix_map) with 
        | Some prefix -> prefix
        | None -> ""
    ) in 
    InductiveRelationD (id, List.map (transform_term prefix_map) types, 
    List.map (fun ((id', bs), prems, terms) -> 
      ((extra_prefix ^ id', transform_binders prefix_map bs), 
        List.map (transform_premise prefix_map) prems, 
        List.map (transform_term prefix_map) terms)
    ) entries)
  | AxiomD (id, bs, rt) -> AxiomD (id, transform_binders prefix_map (improve_ids_binders d.at bs), transform_type prefix_map rt)
  | InductiveFamilyD (id, bs, entries) -> InductiveFamilyD (id, transform_binders prefix_map bs, 
    List.map (fun (terms, t) -> (List.map (transform_term prefix_map) terms, transform_term prefix_map t)) entries)
  | CoercionD (id1, id2, id3) -> CoercionD (id1, id2, id3)
  | UnsupportedD str -> UnsupportedD str
  ) $ d.at
let transform prefix_map mil = 
  List.map (transform_def prefix_map) mil
