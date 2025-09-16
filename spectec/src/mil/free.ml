open Util.Source
open Ast



(* Data Structure *)

module StringSet = Env.StringSet

module VarSet = Set.Make(struct
  type t = ident * mil_typ
  let compare (id1, _typ1) (id2, _typ2) = 
    (* Should have unique ids anyways *)
    String.compare id1 id2
end)

type sets =
  {relid : StringSet.t; varid : StringSet.t; var : VarSet.t}

let empty =
  { 
    relid = StringSet.empty;
    varid = StringSet.empty;
    var = VarSet.empty
  }

let union sets1 sets2 =
  {
    relid = StringSet.union sets1.relid sets2.relid;
    varid = StringSet.union sets1.varid sets2.varid;
    var = VarSet.union sets1.var sets2.var
  }

let diff sets1 sets2 =
  { 
    relid = StringSet.diff sets1.relid sets2.relid;
    varid = StringSet.diff sets1.varid sets2.varid;
    var = VarSet.diff sets1.var sets2.var
  }

let (+) = union
let (-) = diff

let subset sets1 sets2 =
  StringSet.subset sets1.relid sets2.relid &&
  StringSet.subset sets1.varid sets2.varid

let disjoint sets1 sets2 =
  StringSet.disjoint sets1.relid sets2.relid &&
  StringSet.disjoint sets1.varid sets2.varid

let free_relid id = {empty with relid = StringSet.singleton id}
let free_varid id = {empty with varid = StringSet.singleton id}
let free_var id typ = {empty with var = VarSet.singleton (id, typ)}
let _bound_relid id = if id = "_" then empty else free_relid id
let bound_varid id = if id = "_" then empty else free_varid id
let bound_var id typ = if id = "_" then empty else free_var id typ

let free_opt free_x xo = Option.(value (map free_x xo) ~default:empty)
let free_list free_x xs = List.(fold_left (+) empty (map free_x xs))
let bound_list = free_list

let rec free_list_dep free_x bound_x = function
  | [] -> empty
  | x::xs -> free_x x + (free_list_dep free_x bound_x xs - bound_x x)

let rec free_type typ = 
  match typ with
  | T_ident id -> free_varid id
  | T_list ts -> free_list free_term ts
  | T_record_update (t1, _, t2) -> free_term t1 + free_term t2
  | T_record_fields fields -> free_list (fun (_, t) -> free_term t) fields
  | T_lambda (bs, t') -> free_binders bs + (free_term t' - bound_binders bs)
  | T_caseapp (_, ts) -> free_list free_term ts
  | T_dotapp (_, t) -> free_term t
  | T_app ({it = T_ident _id; _ }, ts) -> 
    (* Function call or typ name - avoid putting id on set *) 
    free_list free_term ts
  | T_app (t', ts) -> free_term t' + free_list free_term ts
  | T_app_infix (t1, t2, t3) -> free_term t1 + free_term t2 + free_term t3
  | T_tuple ts -> free_list free_term ts
  | T_tupletype typs -> free_list free_type typs
  | T_arrowtype typs -> free_list free_type typs
  | T_cast (t', typ1, typ2) -> free_term t' + free_type typ1 + free_type typ2
  | _ -> empty

and bound_type typ = 
  match typ with
  | T_ident id -> bound_varid id
  | T_list ts -> bound_list bound_term ts
  | T_record_update (t1, _, t2) -> bound_term t1 + bound_term t2
  | T_record_fields fields -> bound_list (fun (_, t) -> bound_term t) fields
  | T_lambda (bs, t') -> bound_binders bs + bound_term t'
  | T_caseapp (_, ts) -> bound_list bound_term ts
  | T_dotapp (_, t) -> bound_term t
  | T_app ({it = T_ident _id; _ }, ts) -> 
    (* Function call or typ name - avoid putting id on set *) 
    bound_list bound_term ts
  | T_app (t', ts) -> bound_term t' + bound_list bound_term ts
  | T_app_infix (t1, t2, t3) -> bound_term t1 + bound_term t2 + bound_term t3
  | T_tuple ts -> bound_list bound_term ts
  | T_tupletype typs -> bound_list bound_type typs
  | T_arrowtype typs -> bound_list bound_type typs
  | T_cast (t', typ1, typ2) -> bound_term t' + bound_type typ1 + bound_type typ2
  | _ -> empty

and free_term t = 
  (match t.it with
  | T_ident id -> free_varid id + free_var id t.typ
  | _ -> free_type t.it
  ) + free_type t.typ
and bound_term t =
  (match t.it with
  | T_ident id -> bound_varid id + bound_var id t.typ
  | _ -> bound_type t.it
  ) + bound_type t.typ

and free_binder (_i, t) = free_type t
and bound_binder (i, t) = bound_varid i + bound_var i t
and bound_binders bs = free_list bound_binder bs 
and free_binders bs = free_list_dep free_binder bound_binder bs

and free_premise p =
  match p with
  | P_if t -> free_term t
  | P_neg p' -> free_premise p'
  | P_rule (id, terms) -> free_relid id + free_list free_term terms
  | P_list_forall (_, p, b1, v_iter) -> free_binder b1 + (free_premise p - bound_binder b1) + free_term v_iter
  | P_list_forall2 (_, p, b1, b2, v_iter, s_iter) -> free_binder b1 + free_binder b2 + (free_premise p - bound_binder b1 - bound_binder b2) + free_term v_iter + free_term s_iter
  | _ -> empty

(* Function body will be removed later *)
and free_functionbody _fb = empty

and free_record_entry (_p_id, typ) = free_type typ
and bound_record_entry (p_id, _typ) = bound_varid (Print.string_of_prefixed_ident p_id)
and free_inductive_type_entry (_, bs) = free_binders bs
and free_clause_entry (ts, fb) = free_functionbody fb - bound_list bound_term ts
and free_relation_type_entry ((_, bs), prems, ts) = free_binders bs + (free_list free_premise prems + free_list free_term ts - bound_binders bs) 
and free_family_type_entry (_id, b) = free_binder b

and free_def (d : mil_def) = 
  match d.it with
  | TypeAliasD (_, bs, t) -> free_binders bs + (free_type t - bound_binders bs)
  | RecordD (_, bs, entries) -> free_binders bs + (free_list_dep free_record_entry bound_record_entry entries - bound_binders bs)
  | InductiveD (_, bs, entries) -> free_binders bs + (free_list free_inductive_type_entry entries - bound_binders bs)
  | MutualRecD defs -> free_list free_def defs
  | DefinitionD (_, bs, rt, entries) -> free_binders bs + (free_type rt + free_list free_clause_entry entries - bound_binders bs)
  | GlobalDeclarationD (_, rt, entry) -> free_type rt + free_clause_entry entry
  | InductiveRelationD (_, args, entries) -> free_list free_type args + free_list free_relation_type_entry entries
  | AxiomD (_, bs, rt) -> free_binders bs + (free_type rt - bound_binders bs)
  | InductiveFamilyD (_, bs, entries) -> free_binders bs + (free_list free_family_type_entry entries - bound_binders bs)
  | LemmaD (_, bs, prems) -> free_binders bs + (free_list free_premise prems - bound_binders bs)
  | _ -> empty