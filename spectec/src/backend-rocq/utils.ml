open Mil

(* Reserved ids for variables and types *)
let reserved_ids = ["N"; "in"; "In"; 
                    "S";
                    "return";
                    "if";
                    "()"; "tt"; 
                    "Import"; "Export"; 
                    "List"; "String"; 
                    "Type"; "list"; "nat"] |> Env.StringSet.of_list