open Ast

val string_of_atom : atom -> string
val string_of_unop : unop -> string
val string_of_binop : binop -> string
val string_of_cmpop : cmpop -> string
val string_of_brack : brack -> string * string
val string_of_iter : iter -> string
val string_of_typ : typ -> string
val string_of_exp : exp -> string
val string_of_def : def -> string
val string_of_deftyp : deftyp -> string
val string_of_nottyp : nottyp -> string
val string_of_script : script -> string