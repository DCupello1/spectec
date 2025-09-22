open Ast

(* Data Structure *)

module Map = Map.Make(String)

type subst =
  {varid : term Map.t}
type t = subst

let empty =
  { varid = Map.empty;
  }

let mem_varid s id = Map.mem id s.varid
let find_varid s id = Map.find id s.varid

let add_varid s id t = if id = "_" then s else {varid = Map.add id t s.varid}
let remove_varid s id = if id = "_" then s else {varid = Map.remove id s.varid}


let union s1 s2 =
  { varid = Map.union (fun _ _e1 e2 -> Some e2) s1.varid s2.varid;
  }

let remove_varid' s id' = {varid = Map.remove id' s.varid}
let remove_varids s ids' =
  Free.StringSet.(fold (fun id' s -> remove_varid' s id') ids' s)


(* Helpers *)

let subst_opt subst_x s xo = Option.map (subst_x s) xo
let subst_list subst_x s xs = List.map (subst_x s) xs

let rec subst_list_dep subst_x bound_x s = function
  | [] -> [], s
  | x::xs ->
    let x' = subst_x s x in
    let xs', s' = subst_list_dep subst_x bound_x (remove_varids s (bound_x x).Free.varid) xs in
    x'::xs', s'


(* Identifiers *)

let subst_varid s id =
  match Map.find_opt id s.varid with
  | None -> id
  | Some {it = T_ident id'; _} -> id'
  | Some _ -> raise (Invalid_argument "subst_varid")

(* Types *)

let rec subst_term s t = 
  let type_subst = subst_type s t.typ in
  match t.it with
  | T_ident id -> 
    (match Map.find_opt id s.varid with
    | Some e -> e
    | None -> T_ident id $@ type_subst)
  | T_list ts -> T_list (subst_list subst_term s ts) $@ type_subst
  | T_record_update (t1, id, t2) -> T_record_update (subst_term s t1, id, subst_term s t2) $@ type_subst
  | T_record_fields fields -> T_record_fields (subst_list (fun s' (id, t) -> (id, subst_term s' t)) s fields) $@ type_subst 
  | T_caseapp (id, ts) -> T_caseapp (id, subst_list subst_term s ts) $@ type_subst
  | T_dotapp (id, t) -> T_dotapp (id, subst_term s t) $@ type_subst
  | T_app (t', ts) -> T_app (subst_term s t', subst_list subst_term s ts) $@ type_subst
  | T_app_infix (t1, t2, t3) -> T_app_infix (subst_term s t1, subst_term s t2, subst_term s t3) $@ type_subst
  | T_tuple ts -> T_tuple (subst_list subst_term s ts) $@ type_subst
  | T_tupletype typs -> T_tupletype (subst_list subst_type s typs) $@ type_subst
  | T_arrowtype typs -> T_arrowtype (subst_list subst_type s typs) $@ type_subst
  | T_cast (t', typ1, typ2) -> T_cast (subst_term s t', subst_type s typ1, subst_type s typ2) $@ type_subst
  | _ -> t

and subst_type s t = if t = Utils.anytype' then t else (subst_term s (Utils.typ_to_term t)).it
