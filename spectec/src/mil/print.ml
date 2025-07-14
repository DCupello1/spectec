open Ast
open Utils

let parens s = "(" ^ s ^ ")"
let square_parens s = "[" ^ s ^ "]"
let comment_parens s = "(*" ^ s ^ "*)"
let curly_parens s = "{" ^ s ^ "}"

let empty_name s = match s with
  | "" -> "NO_NAME"
  | _ -> s

let string_of_list_prefix prefix delim str_func ls = 
  match ls with
    | [] -> ""
    | _ -> prefix ^ String.concat delim (List.map str_func ls)

let string_of_list_suffix suffix delim str_func ls =
  match ls with
    | [] -> ""
    | _ -> String.concat delim (List.map str_func ls) ^ suffix

let string_of_list prefix suffix delim str_func ls =
  match ls with
    | [] -> ""
    | _ -> prefix ^ String.concat delim (List.map str_func ls) ^ suffix

let string_of_basic_exp_term t = 
  match t with
    | T_bool b -> Bool.to_string b
    | T_nat n -> Z.to_string n
    | T_int i -> Z.to_string i
    | T_rat r -> Q.to_string r
    | T_real r -> Float.to_string r
    | T_string s -> "\"" ^ String.escaped s ^ "\""
    | T_exp_unit -> "()"
    | T_not -> "~"
    | T_and -> " /\\ "
    | T_or -> " \\/ "
    | T_impl -> " -> "
    | T_equiv -> " <-> "
    | T_add -> " + "
    | T_sub -> " - "
    | T_mul -> " * "
    | T_div -> " / "
    | T_exp -> " ^ "
    | T_mod -> " % "
    | T_eq -> " = "
    | T_neq -> " /= "
    | T_lt -> " < "
    | T_gt -> " > "
    | T_le -> " <= "
    | T_ge -> " >= "
    | T_some -> "Option.Some"
    | T_none -> "Option.None"
    | T_recordconcat -> " @ "
    | T_listconcat -> " ++ "
    | T_listcons -> " :: "
    | T_listlength -> "List.length"
    | T_slicelookup -> "List.slice"
    | T_listlookup -> "List.lookup"
    | T_listmember -> "List.member"
    | T_listupdate -> "List.update"
    | T_sliceupdate -> "List.sliceupdate"
    | T_succ -> "S"
    | T_invopt -> "Option.Inv"
    | T_map I_list -> "List.map"
    | T_map I_option -> "Option.map"
    | T_opttolist -> "Option.to_list"
    | T_zipwith I_list -> "List.zipWith"
    | T_zipwith I_option -> "Option.zipWith"

let string_of_basic_type_term t =
  match t with
    | T_unit -> "unit"
    | T_bool -> "bool"
    | T_nat -> "nat"
    | T_int -> "int"
    | T_rat -> "rat"
    | T_real -> "real" (* float? *)
    | T_string -> "string"
    | T_list -> "list"
    | T_opt -> "option"
    | T_anytype -> "Type"
    | T_prop -> "Proposition"

let rec string_of_term t = string_of_term' t.it
and string_of_term' t = 
  match t with 
    | T_exp_basic t_basic -> string_of_basic_exp_term t_basic
    | T_type_basic t_typ_basic -> string_of_basic_type_term t_typ_basic
    | T_ident id -> id
    | T_list terms -> square_parens (String.concat "; " (List.map string_of_term terms))
    | T_lambda (bs, term) -> parens ("fun" ^ string_of_list_prefix " " " " string_of_binder bs ^ " => " ^ string_of_term term)
    | T_record_fields fields -> "{| " ^ String.concat "; " (List.map (fun (id, t) -> id ^ " := " ^ string_of_term t) fields ) ^ " |}"
    | T_caseapp (id, []) -> empty_name id  
    | T_caseapp (id, args) -> parens (empty_name id ^ string_of_list_prefix " " " " string_of_term args)
    | T_dotapp (id, arg) -> parens (empty_name id ^ " " ^ string_of_term arg)
    | T_app (base_term, []) -> empty_name (string_of_term base_term) 
    | T_app (base_term, args) -> parens (empty_name (string_of_term base_term) ^ string_of_list_prefix " " " " string_of_term args)
    | T_app_infix (infix_op, term1, term2) -> parens (string_of_term term1 ^ string_of_term infix_op ^ string_of_term term2)
    | T_tuple [] -> "()"
    | T_tuple terms -> parens (String.concat ", " (List.map string_of_term terms))
    | T_tupletype terms -> parens (String.concat " * " (List.map string_of_term' terms))
    | T_arrowtype terms -> parens (String.concat " -> " (List.map string_of_term' terms))
    | T_cast (term, _, typ) -> parens (string_of_term term ^ " : " ^ string_of_term' typ)
    | T_record_update (t1, id, t3) -> parens ("record_update " ^ string_of_term t1 ^ " " ^ id ^ " " ^ string_of_term t3)
    | T_default -> "default_val"
    | T_unsupported str -> comment_parens ("Unsupported term: " ^ str)

and string_of_binder b = 
  let (id, term) = b in
  parens (id ^ " : " ^ string_of_term' term)

let grab_id_of_binders bs = 
  List.map fst bs

let rec string_of_premise p = 
  match p with
    | P_if term -> string_of_term term
    | P_neg prem -> "~" ^ string_of_premise prem
    | P_rule (ident, terms) -> parens (ident ^ string_of_list_prefix " " " " string_of_term terms)
    | P_else -> "otherwise"
    | P_list_forall (I_list, p, (id, t)) -> 
      let binder = string_of_binder (id, remove_iter_from_type t) in
      "List.Forall " ^ parens ( "fun " ^ binder ^ " => " ^ string_of_premise p) ^ " " ^ id
    | P_list_forall (I_option, p, (id, t)) -> 
      let binder = string_of_binder (id, remove_iter_from_type t) in
      "Option.Forall " ^ parens ( "fun " ^ binder ^ " => " ^ string_of_premise p) ^ " " ^ id
    | P_list_forall2 (I_list, p, (id, t), (id2, t2)) -> 
      let binder = string_of_binder (id, remove_iter_from_type t) in
      let binder2 = string_of_binder (id2, remove_iter_from_type t2) in
      "List.Forall2 " ^ parens ( "fun " ^ binder ^ " " ^ binder2 ^  " => " ^ string_of_premise p) ^ " " ^ id ^ " " ^ id2
    | P_list_forall2 (I_option, p, (id, t), (id2, t2)) -> 
      let binder = string_of_binder (id, remove_iter_from_type t) in
      let binder2 = string_of_binder (id2, remove_iter_from_type t2) in
      "Option.Forall2 " ^ parens ( "fun " ^ binder ^ " " ^ binder2 ^  " => " ^ string_of_premise p) ^ " " ^ id ^ " " ^ id2
    | P_unsupported str -> comment_parens ("Unsupported premise: " ^ str)

let rec string_of_function_body f =
  match f with 
    | F_term term -> string_of_term term
    | F_premises (_, []) -> "True"
    | F_premises (bs, premises) -> string_of_list "forall " ", " " " string_of_binder bs ^ String.concat "/\\" (List.map string_of_premise premises)
    | F_if_else (bool_term, fb1, fb2) -> "if " ^ string_of_term bool_term ^ " then " ^ parens (string_of_function_body fb1) ^ " else\n\t\t\t" ^ parens (string_of_function_body fb2)
    | F_let (var_term, term, fb) -> "let " ^ string_of_term var_term ^ " := " ^ string_of_term term ^ " in\n\t\t\t" ^ string_of_function_body fb
    | F_match term -> string_of_term term (* Todo extend this *)
    | F_default -> "default_term" 

let string_of_inductive_type_entries entries = 
  List.map (fun (id, bs') -> empty_name id ^ string_of_list_prefix " " " " string_of_binder bs') entries

let string_of_family_type_entries _id entries =
  List.map (fun (match_terms, term) -> string_of_list_prefix " " ", " string_of_term match_terms ^ " => " ^ string_of_term term) entries
  
let rec string_of_def ?(suppress_unsup = false) (d : mil_def) =
  let region = ";; " ^ Util.Source.string_of_region d.at ^ "\n" in 
  let endnewline = "\n\n" in

  (match d.it with
    | TypeAliasD (id, binds, term) -> region ^ "type " ^ id ^ string_of_list_prefix " " " " string_of_binder binds ^ " = " ^ string_of_term term ^ endnewline
    | RecordD (id, record_entry) -> region ^ "record " ^ id ^ " = " ^ curly_parens ("\n\t" ^ String.concat ",\n\t" (List.map (fun (id, term) -> 
        id ^ " : " ^ string_of_term term
      ) record_entry) ^ "\n") ^ endnewline
    | InductiveD (id, bs, inductive_type_entries) -> region ^ "inductive " ^ id ^ string_of_list_prefix " " " " string_of_binder bs ^ " : Type =\n\t| " ^
      String.concat "\n\t| " (string_of_inductive_type_entries inductive_type_entries) ^ endnewline
    | DefinitionD (id, bs, rt, clauses) -> region ^ "definition " ^ id ^ string_of_list_prefix " " " " string_of_binder bs ^ " : " ^ string_of_term' rt ^ " =\n\t" ^
      "match " ^ String.concat ", " (grab_id_of_binders bs) ^ " with\n\t\t|" ^
      String.concat "\n\t\t|" (List.map (fun (match_terms, f_b) -> string_of_list_prefix " " ", " string_of_term match_terms ^ " => " ^ string_of_function_body f_b) clauses) ^ endnewline
    | GlobalDeclarationD (id, rt, (_, f_b)) -> region ^ "definition " ^ id ^ " : " ^ string_of_term' rt ^ " := " ^ string_of_function_body f_b ^ endnewline
    | MutualRecD defs -> region ^ String.concat "" (List.map (string_of_def ~suppress_unsup) defs)
    | AxiomD (id, bs, rt) -> region ^ "axiom " ^ id ^ string_of_list_prefix " " " " string_of_binder bs ^ " : " ^ string_of_term' rt ^ endnewline
    | CoercionD (fn_name, typ1, typ2) -> region ^ "coercion " ^ fn_name ^ " : " ^ typ1 ^ " <: " ^ typ2 ^ endnewline
    | UnsupportedD str when not suppress_unsup -> "Unsupported definition: " ^ str
    | InductiveRelationD (id, rel_args, relation_type_entries) -> 
      region ^ "relation " ^ id ^ " : " ^ string_of_list_suffix " -> bool" " -> " string_of_term rel_args ^ " := \n\t| " ^ 
      String.concat "\n\t| " (List.map (fun ((case_id, binds), premises, terms) -> 
          empty_name (case_id) ^ " : " ^ string_of_list "forall " ", " " " string_of_binder binds ^
          string_of_list_suffix " -> " " -> " string_of_premise premises ^ id ^ 
          string_of_list_prefix " " " " string_of_term terms
      
      ) relation_type_entries) ^ endnewline
    | InductiveFamilyD (id, bs, family_type_entries) -> region ^ "definition " ^ id ^ string_of_list_prefix " " " " string_of_binder bs ^ " : Type =\n\t" ^
      "match " ^ String.concat ", " (grab_id_of_binders bs) ^ " with\n\t\t|" ^
      String.concat "\n\t\t|" (string_of_family_type_entries id family_type_entries) ^ endnewline
    | _ -> ""
  )

let string_of_script ds = 
  String.concat "" (List.map (string_of_def ~suppress_unsup:true) ds)