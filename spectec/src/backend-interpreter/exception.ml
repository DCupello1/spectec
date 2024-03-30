exception Trap
exception OutOfMemory
exception Timeout
exception MissingReturnValue of string
exception InvalidArg of string
exception InvalidFunc of string

(* For AL-level debugging *)
exception Error of Util.Source.region * string * string
