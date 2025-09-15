open Util.Source
open Xl.Num

type ident = string

(* binder names *)
type name = ident
type func_name = ident

(* Prefixed name is as follows: list of prefixes that are prepended to the original name *)
type prefixed_ident = ident list * ident

type basic_type = 
  | T_unit
  | T_bool
  | T_nat
  | T_int
  | T_rat
  | T_real
  | T_string
  | T_list
  | T_opt
  | T_anytype (* Generic type for type parameters and types themselves *)
  | T_prop (* Generic type for propositions *)

type basic_term = 
  | T_bool of bool
  | T_nat of nat
  | T_int of int
  | T_rat of rat
  | T_real of real
  | T_string of string
  | T_exp_unit
  | T_not
  | T_and
  | T_or
  | T_impl
  | T_equiv
  | T_add
  | T_sub
  | T_mul
  | T_div
  | T_exp
  | T_mod
  | T_eq
  | T_neq
  | T_lt
  | T_gt
  | T_le
  | T_ge
  | T_some
  | T_none
  | T_recordconcat
  | T_listconcat
  | T_listcons
  | T_listlength
  | T_listmember
  | T_listrepeat
  | T_slicelookup
  | T_listlookup
  | T_listupdate
  | T_sliceupdate
  | T_succ 
  | T_invopt
  | T_opttolist
  | T_map of iterator
  | T_zipwith of iterator

and iterator =
  | I_option
  | I_list

(* MEMO - type themselves don't have a type. Maybe we should fix that? *)
and term = {it : term'; typ: mil_typ}
and term' = 
  | T_exp_basic of basic_term
  | T_type_basic of basic_type
  | T_ident of ident
  | T_list of (term list)
  | T_record_update of (term * prefixed_ident * term)
  | T_record_fields of (prefixed_ident * term) list
  | T_lambda of (binder list * term)
  | T_caseapp of (prefixed_ident * term list)
  | T_dotapp of (prefixed_ident * term) 
  | T_app of (term * term list)
  | T_app_infix of (term * term * term) (* Same as above but first term is placed in the middle *)
  | T_tuple of (term list)
  | T_tupletype of (mil_typ list)
  | T_arrowtype of (mil_typ list)
  | T_cast of (term * mil_typ * mil_typ)
  | T_default
  | T_unsupported of string

and premise =
  | P_if of term
  | P_neg of premise
  | P_rule of ident * term list
  | P_else
  | P_list_forall of iterator * premise * binder
  | P_list_forall2 of iterator * premise * binder * binder
  | P_unsupported of string

and function_body = 
  | F_term of term
  | F_premises of binder list * premise list
  | F_if_else of term * function_body * function_body
  | F_let of term * term * function_body
  | F_match of term (* TODO this one will be tricky *)
  | F_default

and binder = (ident * mil_typ)

and record_entry = (prefixed_ident * mil_typ)

and inductive_type_entry = (prefixed_ident * binder list)

and relation_type_entry = (ident * binder list) * premise list * term list

and relation_args = mil_typ list

and inferred_types = term list 

and mil_typ = term'

and return_type = mil_typ

and clause_entry = term list * function_body 

and family_type_entry = ident * binder

and mil_def = mil_def' phrase
and mil_def' =
  | TypeAliasD of (ident * binder list * mil_typ)
  | RecordD of (ident * binder list * record_entry list)
  | InductiveD of (ident * binder list * inductive_type_entry list)
  | MutualRecD of mil_def list
  | DefinitionD of (ident * binder list * return_type * clause_entry list)
  | GlobalDeclarationD of (ident * return_type * clause_entry)
  | InductiveRelationD of (ident * relation_args * relation_type_entry list)
  | AxiomD of (ident * binder list * return_type)
  | InductiveFamilyD of (ident * binder list * family_type_entry list)
  | CoercionD of (func_name * ident * ident)
  | LemmaD of (ident * binder list * premise list)
  | UnsupportedD of string
  
type mil_script = mil_def list

let ($@) it typ = {it; typ}