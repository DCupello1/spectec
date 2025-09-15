open Ast
open Util.Source


(* Errors *)

let phase = ref "MIL validation"

let error at msg = Util.Error.error at !phase msg


(* Environment *)

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

type mil_deftyp =
  | T_alias of term'
  | T_record of record_entry list
  | T_inductive of inductive_type_entry list
  | T_tfamily of family_type_entry list

type typ_def = binder list * mil_deftyp
type rel_def = relation_args * relation_type_entry list
type def_def = binder list * return_type * clause_entry list

type t =
  {
    typs : typ_def StringMap.t;
    defs : def_def StringMap.t;
    rels : rel_def StringMap.t
  }


(* Operations *)

let empty =
  { 
    typs = StringMap.empty;
    defs = StringMap.empty;
    rels = StringMap.empty;
  }

let mem map id = StringMap.mem id map

let find_opt map id =
  StringMap.find_opt id map

let find space map id at =
  match find_opt map id with
  | None -> error at ("undeclared " ^ space)
  | Some t -> t

let bind _space map id rhs =
  if id = "_" then
    map
  else
    StringMap.add id rhs map

let rebind _space map id rhs =
  assert (StringMap.mem id map);
  StringMap.add id rhs map

let mem_typ env id = mem env.typs id
let mem_def env id = mem env.defs id
let mem_rel env id = mem env.rels id

let find_opt_typ env id = find_opt env.typs id
let find_opt_def env id = find_opt env.defs id
let find_opt_rel env id = find_opt env.rels id

let find_typ env id at = find "type" env.typs id at
let find_def env id at = find "definition" env.defs id at
let find_rel env id at = find "relation" env.rels id at

let bind_typ env id rhs = {env with typs = bind "type" env.typs id rhs}
let bind_def env id rhs = {env with defs = bind "definition" env.defs id rhs}
let bind_rel env id rhs = {env with rels = bind "relation" env.rels id rhs}

let rebind_typ env id rhs = {env with typs = rebind "type" env.typs id rhs}
let rebind_def env id rhs = {env with defs = rebind "definition" env.defs id rhs}
let rebind_rel env id rhs = {env with rels = rebind "relation" env.rels id rhs}

let is_record_typ env id = match (find_opt_typ env id) with 
  | Some (_, T_record _) -> true 
  | _ -> false 

let is_family_typ env id = match (find_opt_typ env id) with 
  | Some (_, T_tfamily _) -> true 
  | _ -> false 

let is_inductive_typ env id = match (find_opt_typ env id) with 
  | Some (_, T_inductive _) -> true 
  | _ -> false 

let is_alias_typ env id = match (find_opt_typ env id) with 
  | Some (_, T_alias _) -> true 
  | _ -> false 

let count_case_binders env typ_id = 
  match (find_opt_typ env typ_id) with
  | Some (dep_bs, T_inductive _) -> List.length dep_bs 
  | _ -> 0

(* Extraction *)

let rec env_of_def env d =
  match d.it with
  | TypeAliasD (id, bs, term) -> bind_typ env id (bs, T_alias term)
  | RecordD (id, bs, records) -> bind_typ env id (bs, T_record records)
  | InductiveD (id, bs, cases) -> bind_typ env id (bs, T_inductive cases)
  | DefinitionD (id, bs, rt, clauses) -> bind_def env id (bs, rt, clauses)
  | GlobalDeclarationD (id, rt, clause) -> bind_def env id ([], rt, [clause])
  | InductiveRelationD (id, r_args, rules) -> bind_rel env id (r_args, rules)
  | AxiomD (id, bs, rt) -> bind_def env id (bs, rt, [])
  | MutualRecD ds -> List.fold_left env_of_def env ds
  | InductiveFamilyD (id, binds, entries) -> 
    bind_typ env id (binds, T_tfamily entries)
  | _ -> env

let env_of_script ds =
  List.fold_left env_of_def empty ds

(* Uniqueness check *)
let check_map map id at =
  match (StringMap.find_opt id map) with
  | Some at' -> error at ("The following id has been defined before: " ^ id ^ "\nAt definition: " ^ string_of_region at')
  | None -> StringMap.add id at map

let rec check_uniqueness_def map d = 
  match d.it with
  | TypeAliasD (id, _, _) | DefinitionD (id, _, _, _) 
  | GlobalDeclarationD (id, _, _) | AxiomD (id, _, _) 
  | InductiveFamilyD (id, _, _) -> 
    map := check_map !map id d.at
  | RecordD (id, _, records) -> 
    List.iter (fun (r_id, _t) -> 
      map := check_map !map (Print.string_of_prefixed_ident r_id) d.at 
    ) records;
    map := check_map !map id d.at
  | InductiveD (id, _bs', cases) -> 
    List.iter (fun (case_id, _bs') -> 
      map := check_map !map (Print.string_of_prefixed_ident case_id)  d.at 
    ) cases;
    map := check_map !map id d.at
  | InductiveRelationD (id, _r_args, rules) -> 
    List.iter (fun ((rule_id, _bs), _prems, _terms) -> 
      map := check_map !map rule_id d.at  
    ) rules;
    map := check_map !map id d.at
  | MutualRecD ds -> List.iter (check_uniqueness_def map) ds
  | _ -> ()

let check_uniqueness ds =
  let case_map = ref StringMap.empty in
  List.iter (check_uniqueness_def case_map) ds

