open Mil.Ast
open Mil

let square_parens s = "[" ^ s ^ "]"
let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"
let comment_parens s = "(* " ^ s ^ " *)"

let family_type_suffix = "entry"

let env_ref = ref Env.empty

let check_trivial_append ident term = 
  match (Env.find_opt_typ !env_ref ident), term with
    | Some (_, T_record _), _ -> true 
    | _, (T_app (T_type_basic T_list, _, _)) -> true
    | _, _ -> false

let is_inductive (d : mil_def) = 
  match d.it with
    | (InductiveRelationD _ | InductiveD _) -> true
    | _ -> false

let comment_desc_def (def: mil_def): string = 
  match def.it with
    | TypeAliasD _ -> "Type Alias Definition"
    | RecordD _ -> "Record Creation Definition"
    | InductiveD _ -> "Inductive Type Definition"
    (* | NotationD _ -> "Notation Definition" *)
    | MutualRecD _ -> "Mutual Recursion"
    | DefinitionD _ -> "Auxiliary Definition"
    | InductiveRelationD _ -> "Inductive Relations Definition"
    | AxiomD _ -> "Axiom Definition"
    | InductiveFamilyD _ -> "Family Type Definition"
    | CoercionD _ -> "Type Coercion Definition"
    | GlobalDeclarationD _ -> "Global Declaration Definition"
    | UnsupportedD _ -> ""

let rec string_of_term (term : term) =
  match term with
    | T_exp_basic (T_bool b) -> string_of_bool b
    | T_exp_basic (T_nat n) -> Z.to_string n
    | T_exp_basic (T_int _i) -> "" (* TODO Manage ints well *)
    | T_exp_basic (T_rat _r) -> "" (* TODO Manage rats well *)
    | T_exp_basic (T_real _r) -> "" (* TODO Manage reals well *)
    | T_exp_basic (T_string s) -> "\"" ^ String.escaped s ^ "\""
    | T_exp_basic T_exp_unit -> "tt"
    | T_exp_basic T_not -> "~"
    | T_exp_basic T_and -> " /\\ "
    | T_exp_basic T_or -> " \\/ "
    | T_exp_basic T_impl -> " -> "
    | T_exp_basic T_equiv -> " <-> "
    | T_exp_basic T_add -> " + "
    | T_exp_basic T_sub -> " - "
    | T_exp_basic T_mul -> " * "
    | T_exp_basic T_div -> " / "
    | T_exp_basic T_exp -> " ^ "
    | T_exp_basic T_mod -> " mod "
    | T_exp_basic T_eq -> " = "
    | T_exp_basic T_neq -> " <> "
    | T_exp_basic T_lt -> " < "
    | T_exp_basic T_gt -> " > "
    | T_exp_basic T_le -> " <= "
    | T_exp_basic T_ge -> " >= "
    | T_exp_basic T_some -> "Some"
    | T_exp_basic T_none -> "None"
    | T_exp_basic T_recordconcat -> " @@ "
    | T_exp_basic T_listconcat -> " ++ "
    | T_exp_basic T_listcons -> " :: "
    | T_exp_basic T_listlength -> "List.length"
    | T_exp_basic T_slicelookup -> "list_slice"
    | T_exp_basic T_listlookup -> "lookup_total"
    | T_exp_basic T_invopt -> "the"
    | T_exp_basic T_succ -> "S"
    | T_exp_basic (T_map I_list) -> "List.map"
    | T_exp_basic (T_map I_option) -> "option_map"
    | T_exp_basic (T_zipwith I_list) -> "list_zipwith"
    | T_exp_basic (T_zipwith I_option) -> "option_zipwith" 
    | T_exp_basic T_listmember -> "List.in" (* TODO check Rocq stdlib *)
    | T_exp_basic T_listupdate -> "list_update_func"
    | T_exp_basic T_opttolist -> "option_to_list"
    | T_exp_basic T_sliceupdate -> "list_slice_update"
    | T_type_basic T_unit -> "unit"
    | T_type_basic T_bool -> "bool"
    | T_type_basic T_nat -> "nat"
    | T_type_basic T_int -> "Z"
    | T_type_basic T_rat -> "Q"
    | T_type_basic T_real -> "R"
    | T_type_basic T_string -> "string"
    | T_type_basic T_list -> "list"
    | T_type_basic T_opt -> "option"
    | T_type_basic T_anytype -> "Type"
    | T_type_basic T_prop -> "Prop"
    | T_ident id -> id
    | T_list [] -> "[]"
    | T_record_fields fields -> "{| " ^ (String.concat "; " (List.map (fun (id, term) -> id ^ " := " ^ string_of_term term) fields)) ^ " |}"
    | T_list entries -> square_parens (String.concat "; " (List.map string_of_term entries))
    | T_match [] -> ""
    | T_match patterns -> parens (String.concat ", " (List.map string_of_term patterns))
    | T_app (base_term, T_app (T_ident _, T_arrowtype _, type_args), args) ->
      let new_args = List.init (List.length type_args) (fun _ -> T_ident "_") @ args in  
      parens ((string_of_term base_term) ^ Mil.Print.string_of_list_prefix " " " " string_of_term new_args)
    | T_app (base_term, _, []) -> (string_of_term base_term) 
    | T_app (base_term, _, args) -> parens ((string_of_term base_term) ^ Mil.Print.string_of_list_prefix " " " " string_of_term args)
    | T_app_infix (infix_op, term1, term2) -> parens (string_of_term term1 ^ string_of_term infix_op ^ string_of_term term2)
    | T_tuple types -> parens (String.concat " * " (List.map string_of_term types))
    | T_record_update (t1, t2, t3) -> parens (string_of_term t1 ^ " <|" ^ string_of_term t2 ^ " := " ^ string_of_term t3 ^ " |>")
    | T_arrowtype terms -> parens (String.concat " -> " (List.map string_of_term terms))
    | T_lambda (ids, term) -> parens ("fun " ^ (String.concat " " ids) ^ " => " ^ string_of_term term)
    | T_cast (term, _, typ) -> parens (string_of_term term ^ " : " ^ string_of_term typ)
    | T_tupletype terms -> parens (String.concat " * " (List.map string_of_term terms))
    | T_unsupported str -> comment_parens ("Unsupported term: " ^ str)

let string_of_binder (id, term) = 
  parens (id ^ " : " ^ string_of_term term)

let string_of_binders (binds : binder list) = 
  Mil.Print.string_of_list_prefix " " " " string_of_binder binds

let string_of_binders_ids (binds : binder list) = 
  Mil.Print.string_of_list_prefix " " " " (fun (id, _) -> id) binds

let string_of_list_type (id : ident) (args : binder list) =
  "Definition " ^ "list__" ^ id ^ string_of_binders args ^ " := " ^ parens ("list " ^ parens (id ^ string_of_binders_ids args))
  
let string_of_option_type (id : ident) (args : binder list) =
  "Definition " ^ "option__" ^ id ^ string_of_binders args ^  " := " ^ parens ("option " ^ parens (id ^ string_of_binders_ids args))

let string_of_match_binders (binds : binder list) =
  parens (String.concat ", " (List.map (fun (id, _) -> id) binds))

let string_of_relation_args (args : relation_args) = 
  Mil.Print.string_of_list_prefix " " " -> " string_of_term args

let rec string_of_premise (prem : premise) =
  match prem with
    | P_if term -> string_of_term term
    | P_rule (id, terms) -> parens (id ^ Mil.Print.string_of_list_prefix " " " " string_of_term terms)
    | P_neg p -> parens ("~" ^ string_of_premise p)
    | P_else -> "otherwise" (* Will be removed by an else pass *)
    | P_list_forall (iterator, p, (id, t)) -> 
      let binder = string_of_binder (id, Mil.Print.remove_iter_from_type t) in
      let option_conversion = if iterator = I_option then "option_to_list " else "" in
      "List.Forall " ^ parens ( "fun " ^ binder ^ " => " ^ string_of_premise p) ^ " " ^ parens (option_conversion ^ id)
    | P_list_forall2 (iterator, p, (id, t), (id2, t2)) -> 
      let binder = string_of_binder (id, Mil.Print.remove_iter_from_type t) in
      let binder2 = string_of_binder (id2, Mil.Print.remove_iter_from_type t2) in
      let option_conversion = if iterator = I_option then "option_to_list " else "" in
      "List.Forall2 " ^ parens ("fun " ^ binder ^ " " ^ binder2 ^ " => " ^ string_of_premise p) ^ " " ^ parens (option_conversion ^ id) ^ " " ^ parens (option_conversion ^ id2)
    | P_unsupported str -> comment_parens ("Unsupported premise: " ^ str)

let rec string_of_function_body f =
  match f with 
    | F_term term -> string_of_term term
    | F_premises (_ ,[]) -> "True"
    | F_premises (bs, prems) -> Mil.Print.string_of_list "forall " ", " " " string_of_binder bs ^ String.concat "/\\" (List.map string_of_premise prems)
    | F_if_else (bool_term, fb1, fb2) -> "if " ^ string_of_term bool_term ^ " then " ^ parens (string_of_function_body fb1) ^ " else\n\t\t\t" ^ parens (string_of_function_body fb2)
    | F_let (var_term, term, fb) -> "let " ^ string_of_term var_term ^ " := " ^ string_of_term term ^ " in\n\t\t\t" ^ string_of_function_body fb
    | F_match term -> string_of_term term (* Todo extend this *)
    | F_default -> "default_val" 

let string_of_typealias (id : ident) (binds : binder list) (typ : term) = 
  "Definition " ^ id ^ string_of_binders binds ^ " := " ^ string_of_term typ ^ ".\n\n" ^ 
  string_of_list_type id binds ^ ".\n\n" ^
  string_of_option_type id binds

let string_of_record (id: ident) (entries : record_entry list) = 
  let constructor_name = "MK" ^ id in

  (* Standard Record definition *)
  "Record " ^ id ^ " := " ^ constructor_name ^ "\n{\t" ^ 
  String.concat "\n;\t" (List.map (fun (record_id, typ) -> 
    record_id ^ " : " ^ string_of_term typ) entries) ^ "\n}.\n\n" ^

  (* Inhabitance proof for default values *)
  "Global Instance Inhabited_" ^ id ^ " : Inhabited " ^ id ^ " := \n" ^
  "{default_val := {|\n\t" ^
      String.concat ";\n\t" (List.map (fun (record_id, _) -> 
        record_id ^ " := default_val") entries) ^ "|} }.\n\n" ^

  string_of_list_type id [] ^ ".\n\n" ^
  string_of_option_type id [] ^ ".\n\n" ^
  (* Record Append proof (TODO might need information on type to improve this) *)
  "Definition _append_" ^ id ^ " (arg1 arg2 : " ^ id ^ ") :=\n" ^ 
  "{|\n\t" ^ String.concat "\t" ((List.map (fun (record_id, term) -> 
    if (check_trivial_append record_id term) 
    then record_id ^ " := " ^ "arg1.(" ^ record_id ^ ") @@ arg2.(" ^ record_id ^ ");\n" 
    else record_id ^ " := " ^ "arg1.(" ^ record_id ^ "); (* FIXME - Non-trivial append*)\n" 
  )) entries) ^ "|}.\n\n" ^ 
  "Global Instance Append_" ^ id ^ " : Append " ^ id ^ " := { _append arg1 arg2 := _append_" ^ id ^ " arg1 arg2 }.\n\n" ^

  (* Setter proof *)
  "#[export] Instance eta__" ^ id ^ " : Settable _ := settable! " ^ constructor_name ^ " <" ^ 
  String.concat ";" (List.map (fun (record_id, _) -> record_id) entries) ^ ">"  

let string_of_inductive_def (id : ident) (args : binder list) (entries : inductive_type_entry list) = 
  "Inductive " ^ id ^ string_of_binders args ^ " : Type :=\n\t" ^
  String.concat "\n\t" (List.map (fun (case_id, binds) ->
    "| " ^ Mil.Print.empty_name case_id ^ string_of_binders binds ^ " : " ^ id ^ string_of_binders_ids args   
  )  entries) ^ ".\n\n" ^

  string_of_list_type id args ^ ".\n\n" ^
  string_of_option_type id args ^ ".\n\n" ^
  (* Inhabitance proof for default values *)
  let inhabitance_binders = string_of_binders args in 
  let binders = string_of_binders_ids args in 
  "Global Instance Inhabited__" ^ id ^ inhabitance_binders ^ " : Inhabited " ^ parens (id ^ binders) ^
  match entries with
    | [] -> "(* FIXME: no inhabitant found! *) .\n" ^
            "\tAdmitted"
    | (case_id, binds) :: _ -> " := { default_val := " ^ (Mil.Print.empty_name case_id) ^ binders ^ 
      Mil.Print.string_of_list_prefix " " " " (fun _ -> "default_val" ) binds ^ " }"

let string_of_definition (prefix : string) (id : ident) (binders : binder list) (return_type : return_type) (clauses : clause_entry list) = 
  prefix ^ id ^ string_of_binders binders ^ " : " ^ string_of_term return_type ^ " :=\n" ^
  "\tmatch " ^ string_of_match_binders binders ^ " with\n\t\t" ^
  String.concat "\n\t\t" (List.map (fun (match_term, fb) -> 
    "| " ^ string_of_term match_term ^ " => " ^ string_of_function_body fb) clauses) ^
  "\n\tend"

let string_of_inductive_relation (prefix : string) (id : ident) (args : relation_args) (relations : relation_type_entry list) = 
  prefix ^ id ^ ":" ^ string_of_relation_args args ^ " -> Prop :=\n\t" ^
  String.concat "\n\t" (List.map (fun ((case_id, binds), premises, end_terms) ->
    let string_prems = Mil.Print.string_of_list_suffix " -> " " -> " string_of_premise premises in
    let forall_quantifiers = Mil.Print.string_of_list "forall " ", " " " string_of_binder binds in
    "| " ^ Mil.Print.empty_name case_id ^ " : " ^ forall_quantifiers ^ string_prems ^ id ^ " " ^ String.concat " " (List.map string_of_term end_terms)
  ) relations)

let string_of_axiom (id : ident) (binds : binder list) (r_type: return_type) =
  "Axiom " ^ id ^ " : forall " ^ string_of_binders binds ^ ", " ^ string_of_term r_type

let string_of_family_types (id : ident) (types: term list) (entries : family_type_entry list) = 
  "Inductive " ^ id ^ " : " ^ Mil.Print.string_of_list_suffix " -> " " -> " string_of_term types ^ "Type :=\n\t| " ^
  String.concat "\n\t| " (List.map (fun (case_id, bs, terms) -> 
    case_id ^ Mil.Print.string_of_list_prefix " " " " string_of_binder bs ^ " : " ^ id ^ Mil.Print.string_of_list_prefix " " " " string_of_term terms) 
  entries)

let string_of_coercion (func_name : func_name) (typ1 : ident) (typ2 : ident) =
  let list_func = "list__" ^ typ1 ^ "__" ^ typ2 in
  let opt_func = "option__" ^ typ1 ^ "__" ^ typ2 in
  "Coercion " ^ func_name ^ " : " ^ typ1 ^ " >-> " ^ typ2 ^ ".\n\n" ^
  "Definition " ^ list_func ^ " : list__" ^ typ1 ^ " -> " ^ "list__" ^ typ2 ^ " := map " ^ func_name ^ ".\n\n" ^
  "Coercion " ^ list_func ^ " : list__" ^ typ1 ^ " >-> " ^ "list__" ^ typ2 ^ ".\n\n" ^
  "Definition " ^ opt_func ^ " : option__" ^ typ1 ^ " -> " ^ "option__" ^ typ2 ^ " := option_map " ^ func_name ^ ".\n\n" ^
  "Coercion " ^ opt_func ^ " : option__" ^ typ1 ^ " >-> " ^ "option__" ^ typ2

let rec string_of_def (recursive : bool) (def : mil_def) = 
  let end_newline = ".\n\n" in 
  let start = comment_parens (comment_desc_def def ^ " at: " ^ Util.Source.string_of_region (def.at)) ^ "\n" in
  match def.it with
    | TypeAliasD (id, binds, typ) -> start ^ string_of_typealias id binds typ ^ end_newline
    | RecordD (id, entries) -> start ^ string_of_record id entries ^ end_newline
    | InductiveD (id, args, entries) -> start ^ string_of_inductive_def id args entries ^ end_newline
    | MutualRecD defs -> start ^ (match defs with
      | [] -> ""
      | [d] -> string_of_def (not (is_inductive d)) d
      | d :: defs -> let prefix = if List.for_all is_inductive (d :: defs) then "\n\nwith\n\n" else "\n\n" in
        string_of_def false d ^ prefix ^ String.concat prefix (List.map (string_of_def true) defs)
      )
    | DefinitionD (id, binds, typ, clauses) -> let prefix = if recursive then "Fixpoint " else "Definition " in
      start ^ string_of_definition prefix id binds typ clauses ^ end_newline
    | GlobalDeclarationD (id, rt, (_, f_b)) -> 
      start ^ "Definition " ^ id ^ " : " ^ string_of_term rt ^ " := " ^ string_of_function_body f_b ^ end_newline
    | InductiveRelationD (id, args, relations) -> let prefix = if recursive then "" else "Inductive " in
      start ^ string_of_inductive_relation prefix id args relations ^ end_newline
    | AxiomD (id, binds, r_type) -> 
      start ^ string_of_axiom id binds r_type ^ end_newline
    | InductiveFamilyD (id, types, entries) -> 
      start ^ string_of_family_types id types entries  ^ end_newline
    | CoercionD (func_name, typ1, typ2) -> 
      start ^ string_of_coercion func_name typ1 typ2 ^ end_newline
    | UnsupportedD _str -> "" (* TODO maybe introduce later if people want it. need to escape "\(*\)" *)

let exported_string = 
  "(* Imported Code *)\n" ^
  "From Coq Require Import String List Unicode.Utf8 Reals.\n" ^
  "From RecordUpdate Require Import RecordSet.\n" ^
  "Require Import NArith.\n" ^
  "Require Import Arith.\n" ^
  "Declare Scope wasm_scope.\n\n" ^
  "Class Inhabited (T: Type) := { default_val : T }.\n\n" ^
  "Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=\n" ^
  "\tList.nth n l default_val.\n\n" ^
  "Definition the {T : Type} {_ : Inhabited T} (arg : option T) : T :=\n" ^
	"\tmatch arg with\n" ^
	"\t\t| None => default_val\n" ^
	"\t\t| Some v => v\n" ^
	"\tend.\n\n" ^
  "Definition list_zipWith {X Y Z : Type} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=\n" ^
  "\tmap (fun '(x, y) => f x y) (combine xs ys).\n\n" ^
  "Definition option_zipWith {α β γ: Type} (f: α → β → γ) (x: option α) (y: option β): option γ := \n" ^
  "\tmatch x, y with\n" ^
  "\t\t| Some x, Some y => Some (f x y)\n" ^
  "\t\t| _, _ => None\n" ^
  "\tend.\n\n" ^
  "Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=\n" ^
  "\tmatch l, n with\n" ^
  "\t\t| nil, _ => nil\n" ^
  "\t\t| x :: l', 0 => y :: l'\n" ^
  "\t\t| x :: l', S n => x :: list_update l' n y\n" ^
  "\tend.\n\n" ^
  "Definition option_append {α: Type} (x y: option α) : option α :=\n" ^
  "\tmatch x with\n" ^
  "\t\t| Some _ => x\n" ^
  "\t\t| None => y\n" ^
  "\tend.\n\n" ^
  "Definition option_map {α β : Type} (f : α -> β) (x : option α) : option β :=\n" ^
	"\tmatch x with\n" ^
	"\t\t| Some x => Some (f x)\n" ^
	"\t\t| _ => None\n" ^
	"\tend.\n\n" ^
  "Fixpoint list_update_func {α: Type} (l: list α) (n: nat) (y: α -> α): list α :=\n" ^
	"\tmatch l, n with\n" ^
	"\t\t| nil, _ => nil\n" ^
	"\t\t| x :: l', 0 => (y x) :: l'\n" ^
	"\t\t| x :: l', S n => x :: list_update_func l' n y\n" ^
	"\tend.\n\n" ^
  "Fixpoint list_slice {α: Type} (l: list α) (i: nat) (j: nat): list α :=\n" ^
	"\tmatch l, i, j with\n" ^
	"\t\t| nil, _, _ => nil\n" ^
	"\t\t| x :: l', 0, 0 => nil\n" ^
	"\t\t| x :: l', S n, 0 => nil\n" ^
	"\t\t| x :: l', 0, S m => x :: list_slice l' 0 m\n" ^
	"\t\t| x :: l', S n, m => list_slice l' n m\n" ^
	"\tend.\n\n" ^
  "Fixpoint list_slice_update {α: Type} (l: list α) (i: nat) (j: nat) (update_l: list α): list α :=\n" ^
	"\tmatch l, i, j, update_l with\n" ^
	"\t\t| nil, _, _, _ => nil\n" ^
	"\t\t| l', _, _, nil => l'\n" ^
	"\t\t| x :: l', 0, 0, _ => nil\n" ^
	"\t\t| x :: l', S n, 0, _ => nil\n" ^
	"\t\t| x :: l', 0, S m, y :: u_l' => y :: list_slice_update l' 0 m u_l'\n" ^
	"\t\t| x :: l', S n, m, _ => x :: list_slice_update l' n m update_l\n" ^
	"\tend.\n\n" ^
  "Definition list_extend {α: Type} (l: list α) (y: α): list α :=\n" ^
  "\ty :: l.\n\n" ^
  "Class Append (α: Type) := _append : α -> α -> α.\n\n" ^
  "Infix \"@@\" := _append (right associativity, at level 60) : wasm_scope.\n\n" ^
  "Global Instance Append_List_ {α: Type}: Append (list α) := { _append l1 l2 := List.app l1 l2 }.\n\n" ^
  "Global Instance Append_Option {α: Type}: Append (option α) := { _append o1 o2 := option_append o1 o2 }.\n\n" ^
  "Global Instance Append_nat : Append (nat) := { _append n1 n2 := n1 + n2}.\n\n" ^
  "Global Instance Inh_unit : Inhabited unit := { default_val := tt }.\n\n" ^
  "Global Instance Inh_nat : Inhabited nat := { default_val := O }.\n\n" ^
  "Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }.\n\n" ^
  "Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.\n\n" ^
  "Global Instance Inh_Z : Inhabited Z := { default_val := Z0 }.\n\n" ^
  "Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.\n\n" ^
  "Definition option_to_list {T: Type} (arg : option T) : list T :=\n" ^
	"\tmatch arg with\n" ^
	"\t\t| None => nil\n" ^
  "\t\t| Some a => a :: nil\n" ^ 
	"\tend.\n\n" ^
  "Coercion option_to_list: option >-> list.\n\n" ^
  "Coercion Z.to_nat: Z >-> nat.\n\n" ^
  "Coercion Z.of_nat: nat >-> Z.\n\n" ^
  "Open Scope wasm_scope.\n" ^
  "Import ListNotations.\n" ^
  "Import RecordSetNotations.\n\n"
  

let string_of_script (mil : mil_script) =
  env_ref := Env.env_of_script mil;
  exported_string ^ 
  "(* Generated Code *)\n" ^
  String.concat "" (List.map (string_of_def false) mil)