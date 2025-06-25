open Il.Ast
open Util.Source

(* HACK This is used to distinguish between normal types and type families *)
let check_normal_type_creation (inst : inst) : bool = 
  match inst.it with
    | InstD (_, args, _) -> List.for_all (fun arg -> 
      match arg.it with 
      (* Args in normal types can really only be variable expressions or type params *)
        | ExpA {it = VarE _; _} | TypA _ -> true
        | _ -> false  
    ) args 

let bind_to_string bind = 
  match bind.it with
    | ExpB (id, _) -> id.it
    | TypB id -> id.it
    | DefB (id, _, _) -> id.it
    | GramB (id, _, _) -> id.it

let sub_type_name binds = (String.concat "_" (List.map bind_to_string binds))


let transform_inst id inst = 
  match inst.it with
    | InstD (binds, _, deftyp) -> (match deftyp.it with 
      | AliasT _ -> []
      | StructT _ | VariantT _ -> 
        (* TODO put correct bindings *)
        let inst = InstD(binds, [], deftyp) $ inst.at in 
        [TypD (id.it ^ sub_type_name binds $ id.at, [], [inst])]
    )

let transform_def def = 
  (match def.it with
     | TypD (id, _, [inst]) when check_normal_type_creation inst -> 
      (* Differenciate normal types from type families through the lack of params *)
      [TypD (id, [], [inst])]
     | TypD (id, _, insts) -> List.concat_map (transform_inst id) insts @ [def.it]
     | d -> [d]
  ) |> List.map (fun d -> d $ def.at) 

let transform (il : script): script = 
  List.concat_map transform_def il