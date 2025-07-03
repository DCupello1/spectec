open Ast
open Env
open Util.Source

let coerce_prefix = "coec_"
let var_prefix = "v_"
let func_prefix = "fun_"

let sub_hastable = Hashtbl.create 16

let get_id_typ term = 
  match term with
    | T_app (T_ident id, T_arrowtype _ , _)
    | T_app (T_ident id, T_type_basic T_anytype, _) -> id
    | _ -> "" 

let rec get_subE_term t =
  match t with
    | T_list terms -> List.concat_map get_subE_term terms
    | T_record_fields fields -> List.concat_map (fun (_, term) -> get_subE_term term) fields
    | T_lambda (_, term) -> get_subE_term term
    | T_match terms -> List.concat_map get_subE_term terms
    | T_app (term, typ, terms) -> get_subE_term term @ get_subE_term typ @ List.concat_map get_subE_term terms
    | T_app_infix (op_term, term1, term2) -> get_subE_term op_term @ get_subE_term term1 @ get_subE_term term2
    | T_tupletype terms -> List.concat_map get_subE_term terms
    | T_arrowtype terms -> List.concat_map get_subE_term terms
    | T_cast (_, typ1, typ2) -> 
      let (id1, id2) = (get_id_typ typ1, get_id_typ typ2) in
      if id1 = "" || id2 = "" then [] else [((id1, typ1), (id2, typ2))]
    | T_record_update (term1, term2, term3) -> get_subE_term term1 @ get_subE_term term2 @ get_subE_term term3
    | T_tuple terms -> List.concat_map get_subE_term terms
    | _ -> [] (* TODO extend to update and extend terms *)

let rec get_subE_prem (premise : premise) =
  match premise with
    | P_rule (_, terms) -> List.concat_map get_subE_term terms
    | P_neg p -> get_subE_prem p
    | P_if term -> get_subE_term term
    | P_list_forall (_, p, _) | P_list_forall2 (_, p, _, _) -> get_subE_prem p
    | _ -> []

let rec is_same_type (t1 : term) (t2 : term) =
  match (t1, t2) with
    (* Normal types *)
    | T_type_basic t1, T_type_basic t2 -> t1 = t2
    (* Tuple types *)
    | T_tupletype terms1, T_tupletype terms2 when List.length terms1 = List.length terms2 -> 
      List.for_all2 is_same_type terms1 terms2
    (* Handle iter types *)
    | T_app (T_type_basic T_list, _, terms1), T_app (T_type_basic T_list, _, terms2) -> 
      List.length terms1 = List.length terms2 && List.for_all2 is_same_type terms1 terms2
    | T_app (T_type_basic T_opt, _, terms1), T_app (T_type_basic T_opt, _, terms2) ->
      List.length terms1 = List.length terms2 && List.for_all2 is_same_type terms1 terms2
    (* Handle user defined types*)
    | T_app (T_ident id1, _, terms1), T_app (T_ident id2, _, terms2) -> 
      id1 = id2 && List.length terms1 = List.length terms2 &&
      List.for_all2 is_same_type terms1 terms2
    | T_ident id, T_ident id2 -> id = id2
    | _ -> false


(* Assumes that tuple variables will be in same order, can be modified if necessary *)
(* TODO must also check if some types inside the type are subtyppable and as such it should also be allowed *)
let find_same_typing (_case_id: ident) (binds: binders) (cases : inductive_type_entry list) =
  List.find_opt (fun (_case_id', binds') -> 
    (* TODO introduce this when we find a better way to check ids *)
    (* (String.ends_with ~suffix:case_id case_id' || String.ends_with ~suffix:case_id' case_id) &&  *)
    List.length binds = List.length binds' &&
    List.for_all2 (fun (typ_id, typ1) (typ_id2, typ2) -> 
      typ_id = typ_id2 && is_same_type typ1 typ2) binds binds'  
  ) cases


let transform_sub_types (at : region) (t1_id : ident) (t1_typ : term) (t2_id : ident) (t2_typ : term) (t1_typ_def : typ_def) (t2_typ_def : typ_def) =
  let func_name = func_prefix ^ coerce_prefix ^ t1_id ^ "__" ^ t2_id in 
  
  [(DefinitionD (func_name, 
    [(var_prefix ^ t1_id, T_app (T_ident t1_id, T_type_basic T_anytype, []))],
    T_app (T_ident t2_id, T_type_basic T_anytype, []), 
    let (_, deftyp) = t1_typ_def in
    let (_, deftyp') = t2_typ_def in
    
    match deftyp, deftyp' with
      | T_inductive cases, T_inductive cases' -> 
        List.map (fun (case_id, bs) ->
          let num_binders = List.length bs in 
          let var_list = List.init num_binders (fun i -> T_ident (var_prefix ^ string_of_int i)) in
          let opt = find_same_typing case_id bs cases' in
          (match opt with
            | Some (case_id', _) -> 
              (T_match [T_app (T_ident case_id, t1_typ, var_list)], F_term (T_app (T_ident case_id', t2_typ, var_list)))
            (* Should find it due to validation *)
            | _ -> error at ("Couldn't coerce type " ^ t1_id ^ " to " ^ t2_id)
          )
        ) cases
      (* Only allowed inductive types for now *)
      | _ -> error at ("Couldn't coerce type " ^ t1_id ^ " to " ^ t2_id)
  ) $ at  ); 
  (CoercionD (func_name, t1_id, t2_id) $ at )]

(* TODO can be extended to other defs if necessary *)
let rec transform_sub_def (env : Env.t) (d : mil_def) = 
  let transform_subE sub_expressions = 
    List.concat_map (fun ((id1, t1), (id2, t2)) -> 
      let combined_name = (id1 ^ "__" ^ id2) in 
      if (Hashtbl.mem sub_hastable combined_name) then []
      else (
        let typ1_cases = find_typ env id1 d.at in
        let typ2_cases = find_typ env id2 d.at in
        Hashtbl.add sub_hastable combined_name combined_name;
        transform_sub_types d.at id1 t1 id2 t2 typ1_cases typ2_cases
    )) sub_expressions 
  in
  match d.it with
    | InductiveRelationD (_, _, rules) -> 
      let sub_expressions = List.concat_map (fun (_, prems, terms) -> List.concat_map get_subE_term terms @ List.concat_map get_subE_prem prems) rules in
      transform_subE sub_expressions @ [d]
    | InductiveFamilyD (_, types, type_family_entries) -> 
      let sub_expressions = List.concat_map get_subE_term types @ 
        List.concat_map (fun (_, bs, terms) -> 
          List.concat_map get_subE_term terms @ List.concat_map (fun (_, t) -> get_subE_term t) bs
        ) type_family_entries in
      transform_subE sub_expressions @ [d]
    | MutualRecD defs -> [MutualRecD (List.concat_map (transform_sub_def env) defs) $ d.at]
    | _ -> [d]

let transform (il : mil_script) =
  List.concat_map (transform_sub_def (env_of_script il)) il