open Util.Source
open Xl.Num

type ident = string

(* binder names *)
type name = ident
type func_name = ident

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
  | T_anytype (* Generic type for type parameters *)

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
  | T_slicelookup
  | T_listlookup
  | T_succ 
  | T_invopt
  | T_map of iterator
  | T_zipwith of iterator

and path_term =
  | P_recordlookup of (ident list * ident)
  | P_listlookup of (ident * term)
  | P_sliceupdate of (ident * term * term)

and iterator =
  | I_option
  | I_list

and term = 
  | T_exp_basic of basic_term
  | T_type_basic of basic_type
  | T_ident of ident list
  | T_update of (path_term list * term * term)
  | T_extend of (path_term list * term * term)
  | T_list of (term list)
  | T_record_fields of (ident * term) list
  | T_lambda of (ident list * term)
  | T_match of (term list)
  | T_app of (term * mil_typ * (term list))
  | T_app_infix of (term * term * term) (* Same as above but first term is placed in the middle *)
  | T_tupletype of (term list)
  | T_arrowtype of (term * term)
  | T_cast of (term * mil_typ * mil_typ)
  | T_unsupported of string

and premise =
  | P_if of term
  | P_neg of premise
  | P_rule of ident * term list
  | P_else
  | P_forall of iterator * premise * ident
  | P_forall2 of iterator * premise * ident * ident
  | P_unsupported of string

and function_body = 
  | F_term of term
  | F_if_else of term * function_body * function_body
  | F_let of term * term * function_body
  | F_match of term (* TODO this one will be tricky *)
  | F_default

and binders = (ident * term) list

and record_entry = (ident * term)

and inductive_type_entry = (ident * binders)

and relation_type_entry = inductive_type_entry * premise list * term list

and relation_args = term list

and inferred_types = term list 

and mil_typ = term

and return_type = term

and clause_entry = term * function_body 

and family_deftype = 
  | TypeAliasT of term
  | InductiveT of inductive_type_entry list


and mil_def = mil_def' phrase
and mil_def' =
  | TypeAliasD of (ident * binders * term)
  | RecordD of (ident * record_entry list)
  | InductiveD of (ident * binders * inductive_type_entry list)
  | MutualRecD of mil_def list
  | DefinitionD of (ident * binders * return_type * clause_entry list)
  | GlobalDeclarationD of (ident * return_type * clause_entry)
  | InductiveRelationD of (ident * relation_args * relation_type_entry list)
  | AxiomD of (ident * binders * return_type)
  | InductiveFamilyD of (ident * family_deftype list)
  | CoercionD of (func_name * ident * ident)
  | UnsupportedD of string
  
type mil_script = mil_def list