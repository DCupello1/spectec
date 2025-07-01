open Mil

(* Reserved ids for variables and types *)
let reserved_ids = ["N"; "in"; "In"; 
                    "S";
                    "()"; "tt"; 
                    "Import"; "Export"; 
                    "List"; "String"; 
                    "Type"; "list"; "nat"] |> Env.Set.of_list