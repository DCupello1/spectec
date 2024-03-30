open Al
open Ast
open Al_util

let ref_type_of =
  (* TODO: some / none *)
  let null = caseV ("NULL", [ optV (Some (listV [||])) ]) in
  let nonull = caseV ("NULL", [ optV None ]) in
  let none = nullary "NONE" in
  let nofunc = nullary "NOFUNC" in
  let noextern = nullary "NOEXTERN" in

  let match_heap_type v1 v2 =
    let open Reference_interpreter in
    let ht1 = Construct.al_to_heap_type v1 in
    let ht2 = Construct.al_to_heap_type v2 in
    Match.match_ref_type [] (Types.Null, ht1) (Types.Null, ht2)
  in

  function
  (* null *)
  | [CaseV ("REF.NULL", [ ht ]) as v] ->
    if match_heap_type none ht then
      CaseV ("REF", [ null; none])
    else if match_heap_type nofunc ht then
      CaseV ("REF", [ null; nofunc])
    else if match_heap_type noextern ht then
      CaseV ("REF", [ null; noextern])
    else
      Numerics.error_typ_value "$ref_type_of" "null reference" v
  (* i31 *)
  | [CaseV ("REF.I31_NUM", [ _ ])] -> CaseV ("REF", [ nonull; nullary "I31"])
  (* host *)
  | [CaseV ("REF.HOST_ADDR", [ _ ])] -> CaseV ("REF", [ nonull; nullary "ANY"])
  (* array/func/struct addr *)
  | [CaseV (name, [ NumV i ])]
  when String.starts_with ~prefix:"REF." name && String.ends_with ~suffix:"_ADDR" name ->
    let field_name = String.sub name 4 (String.length name - 9) in
    let object_ = listv_nth (Ds.Store.access (field_name ^ "S")) (Z.to_int i) in
    let dt = strv_access "TYPE" object_ in
    CaseV ("REF", [ nonull; dt])
  (* extern *)
  (* TODO: check null *)
  | [CaseV ("REF.EXTERN", [ _ ])] -> CaseV ("REF", [ nonull; nullary "EXTERN"])
  | vs -> Numerics.error_values "$ref_type_of" vs
