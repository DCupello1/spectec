open Ast
open Util.Source


(* Errors *)

let phase = ref "validation"

let error at msg = Util.Error.error at !phase msg


(* Environment *)

module Set = Set.Make(String)
module Map = Map.Make(String)

type mil_deftyp =
  | T_alias of term
  | T_record of record_entry list
  | T_inductive of inductive_type_entry list

type typ_def = binders * mil_deftyp
type rel_def = relation_args * relation_type_entry list
type def_def = binders * return_type * clause_entry list

type t =
  {
    typs : typ_def Map.t;
    defs : def_def Map.t;
    rels : rel_def Map.t
  }


(* Operations *)

let empty =
  { 
    typs = Map.empty;
    defs = Map.empty;
    rels = Map.empty;
  }

let mem map id = Map.mem id.it map

let find_opt map id =
  Map.find_opt id map

let find space map id at =
  match find_opt map id with
  | None -> error at ("undeclared " ^ space)
  | Some t -> t

let bind _space map id rhs =
  if id = "_" then
    map
  else
    Map.add id rhs map

let rebind _space map id rhs =
  assert (Map.mem id map);
  Map.add id rhs map

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

(* Extraction *)

let rec env_of_def env d =
  match d.it with
  | TypeAliasD (id, bs, term) -> bind_typ env id (bs, T_alias term)
  | RecordD (id, records) -> bind_typ env id ([], T_record records)
  | InductiveD (id, bs, cases) -> bind_typ env id (bs, T_inductive cases)
  | DefinitionD (id, bs, rt, clauses) -> bind_def env id (bs, rt, clauses)
  | GlobalDeclarationD (id, rt, clause) -> bind_def env id ([], rt, [clause])
  | InductiveRelationD (id, r_args, rules) -> bind_rel env id (r_args, rules)
  | AxiomD (id, bs, rt) -> bind_def env id (bs, rt, [])
  | MutualRecD ds -> List.fold_left env_of_def env ds
  | _ -> env (* TODO extend env to include type families *)

let env_of_script ds =
  List.fold_left env_of_def empty ds
