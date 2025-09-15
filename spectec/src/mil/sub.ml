open Ast
open Env
open Util.Source
open Utils

let coerce_prefix = "coec_"

let sub_hastable = Hashtbl.create 16

let combine_ids id1 id2 = id1 ^ "__" ^ id2

let is_in_sub_hashtable id = Hashtbl.mem sub_hastable id

let get_id_typ term = 
  match term with
  | T_app ({it = T_ident id; _} , _) -> id
  | _ -> "" 

let rec get_subE_term (t : term) = get_subE_term' t.it @ get_subE_term' t.typ
and get_subE_term' t =
  match t with
  | T_list terms -> List.concat_map get_subE_term terms
  | T_record_fields (fields) -> List.concat_map (fun (_, term) -> get_subE_term term) fields
  | T_lambda (_, term) -> get_subE_term term
  | T_caseapp (_id, terms) -> List.concat_map get_subE_term terms
  | T_dotapp (_id, term) -> get_subE_term term
  | T_app (term, terms) -> get_subE_term term @ List.concat_map get_subE_term terms
  | T_app_infix (op_term, term1, term2) -> get_subE_term op_term @ get_subE_term term1 @ get_subE_term term2
  | T_tupletype terms -> List.concat_map get_subE_term' terms
  | T_arrowtype terms -> List.concat_map get_subE_term' terms
  | T_cast (t, typ1, typ2) -> 
    let (id1, id2) = (get_id_typ typ1, get_id_typ typ2) in
    get_subE_term t @ (if id1 = "" || id2 = "" then [] else [((id1, typ1), (id2, typ2))])
  | T_record_update (term1, _, term3) -> get_subE_term term1  @ get_subE_term term3
  | T_tuple terms -> List.concat_map get_subE_term terms
  | _ -> [] 

and get_subE_prem (premise : premise) =
  match premise with
  | P_rule (_, terms) -> List.concat_map get_subE_term terms
  | P_neg p -> get_subE_prem p
  | P_if term -> get_subE_term term
  | P_list_forall (_, p, _) | P_list_forall2 (_, p, _, _) -> get_subE_prem p
  | _ -> []

and get_subE_fb (fb : function_body) = 
  match fb with
  | F_term term -> get_subE_term term
  | F_premises (_bs, prems) -> List.concat_map get_subE_prem prems
  | F_if_else (t, if_fb, else_fb) -> get_subE_term t @ get_subE_fb if_fb @ get_subE_fb else_fb
  | F_let (t1, t2, fb) -> get_subE_term t1 @ get_subE_term t2 @ get_subE_fb fb
  | F_match t -> get_subE_term t
  | _ -> []

let fold_option f terms1 terms2 = 
  List.fold_left2 (fun acc t1 t2 -> 
    match acc with
      | None -> None
      | Some a -> let opt = f t1 t2 in 
        Option.map (fun b -> a @ b) opt
  ) (Some []) terms1 terms2

let rec is_same_type at env (t1 : term) (t2 : term) = is_same_type' at env t1.it t2.it
and is_same_type' at env (t1 : mil_typ) (t2 : mil_typ) =
  match (t1, t2) with
  (* Normal types *)
  | T_type_basic t1, T_type_basic t2 when t1 = t2 -> Some []
  | T_ident id, T_ident id2 when id = id2 -> Some []
  (* Tuple types *)
  | T_tupletype terms1, T_tupletype terms2 when List.length terms1 = List.length terms2 -> 
    fold_option (is_same_type' at env) terms1 terms2
  (* Handle iter types *)
  | T_app ({it = T_type_basic T_list; _}, terms1), T_app ({it = T_type_basic T_list; _}, terms2) 
    when List.length terms1 = List.length terms2 -> 
    fold_option (is_same_type at env) terms1 terms2
  | T_app ({it = T_type_basic T_opt; _}, terms1), T_app ({it = T_type_basic T_opt; _}, terms2)
    when List.length terms1 = List.length terms2 -> 
    fold_option (is_same_type at env) terms1 terms2
  (* Handle user defined types *)
  | T_app ({it = T_ident id1; _}, terms1), T_app ({it = T_ident id2; _}, terms2) 
    when id1 = id2 && List.length terms1 = List.length terms2 -> 
    fold_option (is_same_type at env) terms1 terms2
  | T_caseapp (id1, terms1), T_caseapp (id2, terms2) 
    when id1 = id2 && List.length terms1 = List.length terms2 -> 
    fold_option (is_same_type at env) terms1 terms2
  (* Handle possible subtyping *)
  | T_app ({it = T_ident id1; _}, []), T_app ({it = T_ident id2; _}, []) 
    when is_in_sub_hashtable (combine_ids id1 id2) -> Some []
  | T_app ({it = T_ident id1; _}, []), T_app ({it = T_ident id2; _}, []) ->
    let sub_defs = transform_subE at env [((id1, t1), (id2, t2))] in 
    if sub_defs = [] then None else Some sub_defs
  | _ -> None


(* Assumes that tuple variables will be in same order, can be modified if necessary *)
(* TODO must also check if some types inside the type are subtyppable and as such it should also be allowed *)
and find_same_typing at env ((_prefixes, case_id): prefixed_ident) (binds: binder list) (cases : inductive_type_entry list) =
  List.find_map (fun ((prefixes', case_id'), binds') -> 
    let case_found = case_id = case_id' && List.length binds = List.length binds' in
    if not case_found then None else 
    List.fold_left2 (fun acc t1 t2 -> 
      match acc with
        | None -> None
        | Some (p_id, a) -> let opt = is_same_type' at env t1 t2 in 
          Option.map (fun b -> (p_id, a @ b)) opt
    ) (Some ((prefixes', case_id'), [])) (List.map snd binds) (List.map snd binds')
  ) cases

and transform_sub_types (at : region) (env : Env.t) (t1_id : ident) (t1_typ : term') (t2_id : ident) (t2_typ : term') =
  let (_, deftyp) = find_typ env t1_id at in
  let (_, deftyp') = find_typ env t2_id at in
  let func_name = fun_prefix ^ coerce_prefix ^ t1_id ^ "__" ^ t2_id in 
  let params = [(var_prefix ^ t1_id, T_app (T_ident t1_id $@ anytype', []))] in 
  let return_type = T_app (T_ident t2_id $@ anytype', []) in
  let func clauses = DefinitionD (func_name, params, return_type, clauses) $ at in
  let coercion = CoercionD (func_name, t1_id, t2_id) $ at in 
  let clauses_defs_pair = match deftyp, deftyp' with
  | T_inductive cases, T_inductive cases' -> 
    List.map (fun (case_id, bs) ->
      let var_list = List.mapi (fun i (_, typ) -> T_ident (var_prefix ^ string_of_int i) $@ typ) bs in
      let opt = find_same_typing at env case_id bs cases' in
      (match opt with
        | Some (case_id', defs) -> 
          (([T_caseapp (case_id, var_list) $@ t1_typ], F_term (T_caseapp (case_id', var_list) $@ t2_typ)), defs)
        (* Should find it due to validation *)
        | _ -> error at ("Couldn't coerce type " ^ t1_id ^ " to " ^ t2_id)
      )
    ) cases
  (* Only allowed inductive types for now *)
  | _ -> error at ("Couldn't coerce type " ^ t1_id ^ " to " ^ t2_id) 
  in
  let (clauses, defs) = List.split clauses_defs_pair in
  List.concat defs @ [func clauses; coercion]

and transform_subE at env sub_expressions = 
  List.concat_map (fun ((id1, t1), (id2, t2)) -> 
    let combined_name = combine_ids id1 id2 in 
    if is_in_sub_hashtable combined_name then []
    else (
      Hashtbl.add sub_hastable combined_name combined_name;
      transform_sub_types at env id1 t1 id2 t2
  )) sub_expressions 
  

(* TODO can be extended to other defs if necessary *)
let rec transform_sub_def (env : Env.t) (d : mil_def) =
  match d.it with
  | TypeAliasD (_, _, term) -> 
    let sub_expressions = get_subE_term' term in
    (transform_subE d.at env sub_expressions, d)
  | InductiveRelationD (_, _, rules) -> 
    let sub_expressions = List.concat_map (fun (_, prems, terms) -> List.concat_map get_subE_term terms @ List.concat_map get_subE_prem prems) rules in
    (transform_subE d.at env sub_expressions, d)
  | InductiveFamilyD (_, binders, type_family_entries) -> 
    let sub_expressions = List.concat_map (fun (_, t) -> get_subE_term' t) binders @ 
      List.concat_map (fun (terms, t) -> 
        List.concat_map get_subE_term terms @ get_subE_term t
      ) type_family_entries in
    (transform_subE d.at env sub_expressions, d)
  | DefinitionD (_, _, _, clauses) ->
    let sub_expressions = List.concat_map (fun (terms, fb) ->
      List.concat_map get_subE_term terms @ get_subE_fb fb
    ) clauses in 
    (transform_subE d.at env sub_expressions, d)
  | MutualRecD defs -> 
    let defs', ds = List.split (List.map (transform_sub_def env) defs) in
    (List.concat defs', MutualRecD ds $ d.at)
  (* | MutualRecD defs -> [MutualRecD (List.concat_map (transform_sub_def env) defs) $ d.at] *)
  | _ -> ([], d)

let transform (mil : mil_script) =
  List.concat_map (fun d -> 
    let (new_defs, d') = transform_sub_def (env_of_script mil) d in 
    new_defs @ [d']
  ) mil