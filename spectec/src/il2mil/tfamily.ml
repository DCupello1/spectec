open Il.Ast
open Util.Source
open Util

let type_family_prefix = "CASE_"
let name_prefix id = id.it ^ "_" 
let error at msg = Error.error at "MIL Preprocessing" msg

let make_arg b = 
  (match b.it with
  | ExpB (id, typ) -> ExpA (VarE id $$ id.at % typ) 
  | TypB id -> TypA (VarT (id, []) $ id.at) (* TODO unsure this makes sense*)
  | DefB (id, _, _) -> DefA id 
  | GramB (_, _, _) -> assert false (* Avoid this *)
  ) $ b.at

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

let sub_type_name_binds binds = (String.concat "_" (List.map bind_to_string binds))
  
(* Creates new TypD's for each StructT and VariantT *)
let create_types id inst = 
  let make_param_from_bind b = 
  (match b.it with 
  | ExpB (id, typ) -> ExpP (id, typ)
  | TypB id -> TypP id
  | DefB (id, params, typ) -> DefP (id, params, typ)
  | GramB _ -> assert false (* Avoid this *)
  ) $ b.at in
  match inst.it with
  | InstD (binds, _, deftyp) -> 
    (match deftyp.it with 
    | AliasT _ -> []
    | StructT _ | VariantT _ ->
      let inst = InstD(binds, List.map make_arg binds, deftyp) $ inst.at in 
      [TypD (id.it ^ sub_type_name_binds binds $ id.at, List.map make_param_from_bind binds, [inst])]
    )

let rec transform_type_family def =
  (match def.it with
  | TypD (id, params, [inst]) when check_normal_type_creation inst -> [TypD (id, params, [inst])]
  | TypD (id, params, insts) -> let types = List.concat_map (create_types id) insts in
    let transformed_instances = List.map (fun inst -> match inst.it with 
      | InstD (binds, args, {it = StructT _; at; _}) | InstD(binds, args, {it = VariantT _; at; _}) -> 
        InstD (binds, args, AliasT (VarT (id.it ^ sub_type_name_binds binds $ id.at, List.map make_arg binds) $ id.at) $ at) $ inst.at
      | _ -> inst 
    ) insts in
    types @ [TypD(id, params, transformed_instances)]
  | RecD defs -> [RecD (List.concat_map transform_type_family defs)]
  | d -> [d]
  ) |> List.map (fun d -> d $ def.at)

let transform (il : script): script = 
  let il_transformed = List.concat_map transform_type_family il in
  il_transformed