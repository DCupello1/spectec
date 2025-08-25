open Ast

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

(* Prefixes used everywhere in MIL *)
let var_prefix = "v_"
let fun_prefix = "fun_"

let anytype' = T_type_basic T_anytype
let anytype = anytype' $@ anytype'

let typ_to_term t = t $@ anytype'

let string_combine id typ_name = id ^ "__" ^ typ_name

let num_typ nt = T_arrowtype [nt; nt; nt]

let bool_binop_typ = T_arrowtype [T_type_basic T_bool; T_type_basic T_bool; T_type_basic T_bool]
let prop_binop_typ = T_arrowtype [T_type_basic T_prop; T_type_basic T_prop; T_type_basic T_prop]

let remove_iter_from_type t =
  match t with
  | T_app ({it = T_type_basic T_list; _}, [t']) -> t'.it
  | T_app ({it = T_type_basic T_opt; _}, [t']) -> t'.it
  | t' -> t'

let get_id t = 
  match t with
  | T_app ({it = T_ident id; _}, _) -> id
  | _ -> assert false

let has_parameters t =
  match t with
  | T_app ({it = T_ident _; _}, args) -> args <> []
  | _ -> false 