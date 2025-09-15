open Ast
module StringSet = Env.StringSet

module VarSet : Set.S with type elt = string * term'

type sets = { relid : StringSet.t; varid : StringSet.t; var : VarSet.t}

val empty : sets
val union : sets -> sets -> sets
val diff : sets -> sets -> sets
val subset : sets -> sets -> bool
val disjoint : sets -> sets -> bool

val free_relid : StringSet.elt -> sets
val free_varid : StringSet.elt -> sets

val free_opt : ('a -> sets) -> 'a option -> sets
val free_list : ('a -> sets) -> 'a list -> sets

val free_type : term' -> sets
val free_term : term -> sets
val free_binders : binder list -> sets
val free_premise : premise -> sets
val free_functionbody : function_body -> sets
val free_record_entry : record_entry -> sets
val free_inductive_type_entry : inductive_type_entry -> sets
val free_clause_entry : clause_entry -> sets
val free_relation_type_entry : relation_type_entry -> sets
val free_family_type_entry : family_type_entry -> sets
val free_def : mil_def -> sets
