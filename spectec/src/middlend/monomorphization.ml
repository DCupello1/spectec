(* TODO - Make sure we are applying the right regions at the right spots (necessary for debugging later) *)
(* TODO - Improve eval reduction function to reduce function calls correctly (can't have function calls with irreducible arguments actually be reduced) *)
open Il.Ast
open Il.Print
open Il
open Il.Eval
open Util.Source
open Util.Error
open Xl

(* Exception raised when a dependent type depends on unbounded arguments *)
exception UnboundedArg of string

(* Env Creation and utility functions *)

module StringMap = Map.Make(String)
module IdSet = Set.Make(String)

module ExpSet = Set.Make(struct
  type t = Il.Ast.exp
  let compare exp1 exp2 = if Il.Eq.eq_exp exp1 exp2 then 0 
    else String.compare (string_of_exp exp1) (string_of_exp exp2) (* HACK - Need better way to compare expressions, only hurts performance *)
end
)

module TypSet = Set.Make(struct
  type t = Il.Ast.typ
  let compare typ1 typ2 = if Il.Eq.eq_typ typ1 typ2 then 0 
    else String.compare (string_of_typ typ1) (string_of_typ typ2) (* HACK - Need better way to compare types, only hurts performance *)
end
)

type monoenv = 
{
  mutable calls: (ExpSet.t ref) StringMap.t;
  mutable concrete_dependent_types: (TypSet.t ref) StringMap.t;
  mutable il_env: env;
  mutable mono_list: def list;
  mutable nat_subs_set: (Num.nat list) StringMap.t
}

let new_env = 
{
  calls = StringMap.empty;
  concrete_dependent_types = StringMap.empty;
  il_env = Il.Env.empty;
  mono_list = [];
  nat_subs_set = StringMap.empty
}

let mono = "Monomorphization"

let empty_tuple_exp at = TupE [] $$ at % (TupT [] $ at)

let map_snd f = List.map (fun (v1, v2) -> (v1, f v2))

let msg_prefix = "Encountered an unbounded type: "


let _unbounded_error at msg = error at mono (msg_prefix ^ msg)

let print_env (m_env : monoenv) = 
  print_endline "Printing the Env: ";
  print_endline " ";

  print_endline "Function calls:";
  StringMap.iter (fun id exps -> 
    print_string ("Set with key " ^ id ^ "{");
    print_string (String.concat ", " (List.map string_of_exp (ExpSet.elements !exps)));
    print_endline "}") m_env.calls;
  
  print_endline "Dependent Types:";
  StringMap.iter (fun id typs -> 
    print_string ("Set with key " ^ id ^ "{");
    print_string (String.concat ", " (List.map string_of_typ (TypSet.elements !typs)));
    print_endline "}") m_env.concrete_dependent_types;
  
  print_endline "Mono nat subsets:";
  StringMap.iter (fun id nat_list -> print_endline (id ^ " : [" ^ String.concat ", " (List.map Z.to_string nat_list) ^ "]")) m_env.nat_subs_set

let bind_typ m_env' id t =
  if id = "_" then m_env' else
    match StringMap.find_opt id m_env' with 
      | None -> StringMap.add id (ref (TypSet.singleton t)) m_env'
      | Some set -> set := TypSet.add t !set; m_env'

let bind_exp m_env' id t =
  if id = "_" then m_env' else
    match StringMap.find_opt id m_env' with 
      | None -> StringMap.add id (ref (ExpSet.singleton t)) m_env'
      | Some set -> set := ExpSet.add t !set; m_env'

let add_to_mono_list (m_env : monoenv) (def : def): unit =
  m_env.mono_list <- def :: m_env.mono_list 
      
let concrete_dep_types_bind m_env id t =
  m_env.concrete_dependent_types <- bind_typ m_env.concrete_dependent_types id t

let function_calls_bind m_env id t =
  m_env.calls <- bind_exp m_env.calls id t

let partition_mapi p l =
  let rec part left right i = function
  | [] -> (List.rev left, List.rev right)
  | x :: l ->
      begin match p x i with
        | Either.Left v -> part (v :: left) right (i + 1) l
        | Either.Right v -> part left (v :: right) (i + 1)  l
      end
  in
  part [] [] 0 l

let partition_map_using_tail p l =
  let rec part left right = function
  | [] -> (List.rev left, List.rev right)
  | x :: l ->
      begin match p x l with
        | Either.Left v -> part (v :: left) right l
        | Either.Right v -> part left (v :: right) l
      end
  in
  part [] [] l

let filter_map_using_taili f =
  let rec aux accu i = function
    | [] -> List.rev accu
    | x :: l ->
        match f x l i with
        | None -> aux accu (i + 1) l
        | Some v -> aux (v :: accu) (i + 1) l
  in
  aux [] 0

let map_bool_to_either (a: 'a) (b : bool): ('a, 'a) Either.t =
  if b then Either.Left a else Either.Right a

let map_bool_to_option (a: 'a) (b : bool): 'a option =
  if b then Some a else None

let reduce_arg (env : Il.Env.t) (arg : arg): arg = 
  (match arg.it with
    | ExpA exp -> ExpA (Il.Eval.reduce_exp env exp)
    | TypA typ -> TypA (Il.Eval.reduce_typ env typ)
    | a -> a
  ) $ arg.at
  
(* Computes the cartesian product of a given list. *)
let product_of_lists (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> v :: existing) lst) acc) [[]] lists

let product_of_lists_append (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> existing @ [v]) lst) acc) [[]] lists

let transform_atom (a : atom) = 
  match a.it with
    | Atom s -> s
    | _ -> ""

let is_atomid (a : atom) =
  match a.it with
    | Atom _ -> true
    | _ -> false

(* String transformation Args *)
let to_string_mixop (m : mixop) = match m with
  | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> a
  | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )

let rec to_string_exp (exp : exp) : string = 
  match exp.it with
    | BoolE _ | NumE _ | TextE _ -> string_of_exp exp
    | ListE exps -> "l" ^ String.concat "_" (List.map to_string_exp exps) 
    | TupE [] -> ""
    | TupE exps -> String.concat "_" (List.map to_string_exp exps) 
    | CaseE (mixop, {it = TupE []; _}) -> to_string_mixop mixop 
    | CaseE (_mixop, exp) -> to_string_exp exp
    | CvtE (e, _, _) -> to_string_exp e
    | SubE (e, _, _) -> to_string_exp e
    | _ -> assert false
    (* | _ -> error exp.at mono ("Cannot transform " ^ string_of_exp exp ^ " into string") *)

and to_string_typ (typ : typ) : string = 
  match typ.it with
    | BoolT | NumT _ | TextT -> string_of_typ typ
    | VarT (id, args) -> id.it ^ "_" ^ String.concat "_" (List.map to_string_arg args)
    | IterT (typ, iter) -> string_of_typ typ ^ "_" ^ string_of_iter iter
    | TupT [] -> ""
    | TupT exp_typ_pairs -> "tt" ^ String.concat "_" (List.map (fun (e, t) -> to_string_exp e ^ to_string_typ t) exp_typ_pairs) 

and to_string_arg (arg : arg): string =
  match arg.it with
    | ExpA exp -> to_string_exp exp
    | TypA typ -> to_string_typ typ
    | _ -> ""

and transform_id_from_args (id : id) (args : arg list): id =
  if args = [] then id else 
  id.it ^ "_mono_" ^ String.concat "_" (List.map to_string_arg args) $ id.at

and transform_string_from_exps (text : string) (exps : exp list): string =
  if exps = [] then text else 
  text ^ "_mono_" ^ (String.concat "_" (List.map to_string_exp exps))

and transform_id_from_exps (m_env : monoenv) (id : id) (exps : exp list): id =
  transform_string_from_exps id.it (List.map (Il.Eval.reduce_exp m_env.il_env) exps) $ id.at

(* TODO fix this to remove the correct holes in the more complicated case *)
and transform_mixop (m_env : monoenv) (m : mixop) (num_kept : int) (exps : exp list) : mixop =
  if exps = [] then m else
  let reduced_exps = List.map (Il.Eval.reduce_exp m_env.il_env) exps in
  match m with
    | [{it = Atom.Atom a; _} as atom]::tail when List.for_all ((=) []) tail -> 
      [Atom.Atom (transform_string_from_exps a reduced_exps) $$ atom.at % atom.note]::(List.init num_kept (fun _ -> []))
    | _ -> 
      let rec aux num_empty = function
        | [] -> []
        | [] :: ls when num_empty > num_kept -> aux (num_empty + 1) ls
        | [] :: ls -> [] :: aux (num_empty + 1) ls
        | _ :: ls -> aux num_empty ls
      in
      List.mapi (fun i atoms -> 
      let length_last = List.length m in 
      let new_atom = Atom.Atom (transform_string_from_exps "" reduced_exps) $$ (no_region, Atom.info "") in
      if i = length_last - 1 then atoms @ [new_atom] else atoms) (aux 0 m)

let create_args_pairings (args_ids : id list) (concrete_args : arg list): subst =
  List.fold_left (fun acc (id, arg) -> 
    if id.it = "_" then acc else
    match arg.it with
    | ExpA exp -> Il.Subst.add_varid acc id exp
    | TypA typ -> Il.Subst.add_typid acc id typ
    | DefA x -> Il.Subst.add_defid acc id x
    | GramA g -> Il.Subst.add_gramid acc id g) Il.Subst.empty (List.combine args_ids concrete_args)

(* Terminal cases traversal *)
let rec check_reducible_exp (exp : exp) : bool =
  match exp.it with
    | BoolE _ | NumE _ | TextE _ -> true
    | UnE (_, _, e) -> check_reducible_exp e
    | BinE (_, _, e1, e2) -> check_reducible_exp e1 && check_reducible_exp e2
    | CmpE (_, _, e1, e2) -> check_reducible_exp e1 && check_reducible_exp e2
    | TupE exps -> List.for_all check_reducible_exp exps 
    | CvtE (e, _, _) -> check_reducible_exp e
    | SubE (e, _, _) -> check_reducible_exp e
    | ListE exps -> List.for_all check_reducible_exp exps 
    | CaseE (_, e) -> check_reducible_exp e
    | CallE (_, args) -> List.for_all check_reducible_arg args
    | TheE e -> check_reducible_exp e
    | _ -> false

and check_reducible_arg (arg: arg): bool =
  match arg.it with
    | TypA _ -> true
    | ExpA exp -> check_reducible_exp exp
    | _ -> false

and check_reducible_args (args: arg list): bool =
  List.for_all check_reducible_arg args

(* Simple getters which traverse part of the AST *)
let get_dependent_type_args (typ : typ): arg list = 
  match typ.it with  
    | VarT (_, concrete_args) -> concrete_args
    | _ -> error typ.at mono "Applied monomorphization on a non-concrete dependent type"

let get_function_call (exp : exp): id * arg list =
  match exp.it with
    | CallE (id, args) -> (id, args)
    | _ -> error exp.at mono "Applied monomorphization on a non-function call expression"

let rec get_variable_id_safe (exp : exp): id = 
  match exp.it with
    | VarE id -> id
    | IterE (e, _) -> get_variable_id_safe e
    | SubE (e, _, _) -> get_variable_id_safe e
    | _ -> "" $ no_region

let get_variable_id_from_param (param : param): id =
  match param.it with
    | ExpP (id, _) -> id
    | TypP id -> id
    | DefP (id, _, _) -> id
    | GramP (id, _) -> id

let get_tuple_from_type (typ : typ): ((exp * typ) list) option =
  match typ.it with
    | TupT [] -> None
    | TupT e_t -> Some e_t
    | _ -> None (* We don't need to worry about the case of it being single typed *)
  
let get_user_defined_type_arguments (args : arg list): string list =
  let rec get_func_typ typ = 
    match typ.it with 
      | VarT (id, args) -> id.it :: List.concat_map get_func_arg args 
      | IterT (typ, _) -> get_func_typ typ
      | TupT exp_typ_pairs -> List.concat_map (fun (_, t) -> get_func_typ t) exp_typ_pairs
      | _ -> []
  and get_func_arg arg = 
    match arg.it with
      | TypA typ -> get_func_typ typ
      | _ -> [] (* TODO extend this later to exps *)
  in 
  List.filter_map (fun a ->
    match a.it with
      | TypA typ -> (* Has to start with type argument *) Some (get_func_typ typ)
      | _ -> None
  ) args |> List.concat

let rec get_all_dep_types_in_typ (t : typ): (id * arg list) list = 
  match t.it with
    | VarT (id, args) -> (id, args) :: List.concat_map get_all_dep_types_in_arg args 
    | TupT exp_typ_pairs -> List.concat_map (fun (_, t) -> get_all_dep_types_in_typ t) exp_typ_pairs
    | IterT (typ, _) -> get_all_dep_types_in_typ typ
    | _ -> []

and get_all_dep_types_in_arg (arg : arg): (id * arg list) list =
  match arg.it with
    | ExpA exp -> get_all_dep_types_in_exp exp
    | TypA typ -> get_all_dep_types_in_typ typ
    | _ -> []

and get_all_dep_types_in_bind (bind : bind): (id * arg list) list = 
  match bind.it with
    | ExpB (_, typ) -> get_all_dep_types_in_typ typ
    | _ -> []

and get_all_dep_types_in_exp (exp : exp): (id * arg list) list =
  let r_func = get_all_dep_types_in_exp in
  get_all_dep_types_in_typ exp.note @ 
  match exp.it with
    | CaseE (_, e) -> r_func e
    | CallE (_, args) -> List.concat_map get_all_dep_types_in_arg args
    | UnE (_, _, e) -> r_func e
    | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2) -> r_func e1 @ r_func e2
    | TupE exps | ListE exps -> List.concat_map r_func exps
    | ProjE (e, _) -> r_func e
    | UncaseE (e, _) -> r_func e
    | OptE (Some e) -> r_func e
    | TheE e -> r_func e
    | StrE expfields -> List.concat_map (fun (_, e) -> r_func e) expfields
    | DotE (e, _) -> r_func e
    | CompE (e1, e2) -> r_func e1 @ r_func e2
    | LiftE e -> r_func e
    | MemE (e1, e2) -> r_func e1 @ r_func e2
    | LenE e -> r_func e
    | CatE (e1, e2) -> r_func e1 @ r_func e2
    | IdxE (e1, e2) -> r_func e1 @ r_func e2
    | SliceE (e1, e2, e3) -> r_func e1 @ r_func e2 @ r_func e3
    | UpdE (e1, p, e2) | ExtE (e1, p, e2) -> r_func e1 @ get_all_dep_types_in_path p @ r_func e2
    | IterE (e1, (_, id_exp_pairs)) -> r_func e1 @ List.concat_map (fun (_, e) -> r_func e) id_exp_pairs
    | CvtE (e1, _, _) | SubE (e1, _, _) -> r_func e1 
    | _ -> []

and get_all_dep_types_in_path (path : path): (id * arg list) list =
  match path.it with
    | RootP -> []
    | IdxP (p, e) -> get_all_dep_types_in_path p @ get_all_dep_types_in_exp e
    | SliceP (p, e1, e2) -> get_all_dep_types_in_path p @ get_all_dep_types_in_exp e1 @ get_all_dep_types_in_exp e2
    | DotP (p, _) -> get_all_dep_types_in_path p

and get_all_dep_types_in_prem (prem : prem): (id * arg list) list = 
  match prem.it with
    | RulePr (_, _, exp) | IfPr exp -> get_all_dep_types_in_exp exp
    | LetPr (exp1, exp2, _) -> get_all_dep_types_in_exp exp1 @ get_all_dep_types_in_exp exp2
    | IterPr (p, (_, id_exp_pairs)) -> get_all_dep_types_in_prem p @ 
      List.concat_map (fun (_, e) -> get_all_dep_types_in_exp e) id_exp_pairs
    | _ -> []
    
(* Gets the inductive case that the given mixop is referring. Goes through type aliases if necessary *)
let rec get_case_instance_safe (m_env : monoenv) (mixop : mixop) (inst : inst): typcase option =
  match inst.it with
    | InstD (_, _, deftyp) -> match deftyp.it with
      | VariantT typcases -> List.find_opt (fun (m, _, _) -> Xl.Mixop.eq mixop m) typcases
      | AliasT {it = VarT (id, _); _} -> let (_, insts) = Il.Env.find_typ m_env.il_env id in 
        (match insts with 
          | [inst] -> get_case_instance_safe m_env mixop inst
          | _ -> None
        )
      | _ -> None
  
let get_case_instance (m_env : monoenv) (mixop : mixop) (at : Util.Source.region) (inst : inst): typcase = 
  match (get_case_instance_safe m_env mixop inst) with
    | Some typcase -> typcase
    | None -> error at mono ("Case cannot be found for mixop " ^ string_of_mixop mixop)

(* Dependent type check traversal *)

let rec check_dep_type (t : typ): bool = 
  match t.it with
    | VarT (_ , []) -> false
    | VarT (_, _) -> true
    | IterT (t, _) -> check_dep_type t
    | TupT exp_typ_pairs -> List.map snd exp_typ_pairs |> List.exists check_dep_type
    | _ -> false

and check_dep_typ_in_bind (b : bind): bool = 
  match b.it with
    | ExpB (_, typ) -> check_dep_type typ
    | _ -> false

and check_dep_typ_in_params (p : param): bool = 
  match p.it with
    | ExpP (_, typ) -> check_dep_type typ
    | _ -> false

(* Family of functions that split types into two buckets: 
 * - ids that are used in dependent types 
 * - the rest (normal types or depedent types)
 * These are used extensively to perform monomorphization on the given "used" types
*)
let split_used_dependent_types_case_args (exp_typ_pairs : (exp * typ) list): (exp * typ) list * (exp * typ) list =
  partition_map_using_tail (fun ((e, _) as p) ps -> 
    let free_vars_pairs = (Free.free_list (fun (_, t) -> Free.free_typ t) ps).varid in
    let free_vars_pair = (Free.free_exp e).varid in  
    map_bool_to_either p (not (Free.Set.is_empty (Free.Set.inter free_vars_pairs free_vars_pair)))
  ) exp_typ_pairs

let split_used_dependent_types_case_args_index (exp_typ_pairs : (exp * typ) list): int list =
  filter_map_using_taili (fun (e, _) ps i -> 
    let free_vars_pairs = (Free.free_list (fun (_, t) -> Free.free_typ t) ps).varid in
    let free_vars_pair = (Free.free_exp e).varid in
    map_bool_to_option i (not (Free.Set.is_empty (Free.Set.inter free_vars_pairs free_vars_pair)))
  ) exp_typ_pairs

let split_used_dependent_types_relation_binds (binds : bind list) (exp : exp) (prems: prem list): bind list * bind list =
  let dep_ids_in_relation = get_all_dep_types_in_exp exp @ List.concat_map get_all_dep_types_in_prem prems 
    |> List.map snd
    |> Free.free_list (fun args -> Free.free_list Free.free_arg args) 
  in
  partition_map_using_tail (fun b bs ->
    match b.it with
      | ExpB (id, _) -> 
        let dep_ids_in_binds = (Free.free_list Free.free_bind (List.filter check_dep_typ_in_bind bs)).varid in
        let dep_ids_union = Free.Set.union dep_ids_in_relation.varid dep_ids_in_binds in
        map_bool_to_either b (Free.Set.mem id.it dep_ids_union)
      | _ -> Right b 
  ) binds
      
let split_used_types_in_params (params : param list) (return_type : typ): param list * param list = 
  partition_map_using_tail (fun p ps -> 
    let is_type_param, id_p = match p.it with
        | ExpP (id, _) -> false, id.it
        | TypP id -> true, id.it
        | _ -> false, ""
    in
    let free_vars_params = (Free.free_list Free.free_param (List.filter check_dep_typ_in_params ps)).varid in
    let free_vars_rt = (Free.free_typ return_type).varid in
    map_bool_to_either p (is_type_param || Free.Set.mem id_p (Free.Set.union free_vars_params free_vars_rt))
  ) params

let split_used_types_in_params_index (params : param list) (return_type : typ option): int list = 
  filter_map_using_taili (fun p ps i ->
    let is_type_param, id_p = match p.it with
      | ExpP (id, _) -> false, id.it
      | TypP id -> true, id.it
      | _ -> false, ""
    in
    let return_typ_ids = match return_type with
      | None -> Free.Set.empty
      | Some typ -> (Free.free_typ typ).varid
    in
    let free_vars_params = (Free.free_list Free.free_param (List.filter check_dep_typ_in_params ps)).varid in
    map_bool_to_option i (is_type_param || Free.Set.mem id_p (Free.Set.union free_vars_params return_typ_ids))
  ) params

let split_used_types_in_type_creation (m_env : monoenv) (mixop : mixop) (insts: inst list) (exps : exp list) (at: Util.Source.region): exp list * exp list =
  match insts with
    | [inst] when Mono_nat_subset.check_normal_type_creation inst -> 
      let (_, (_, t, _), _) = get_case_instance m_env mixop at inst in
      (match (get_tuple_from_type t) with 
        | None -> ([], exps)
        | Some exp_typ_pairs -> 
          let used_indices = split_used_dependent_types_case_args_index exp_typ_pairs in
          partition_mapi (fun e i -> map_bool_to_either e (List.mem i used_indices)) exps
      )
    | _ -> ([], exps)

let _check_used_dependent_types_in_case_exp (exps : exp list) (case_typ : typ) : exp list * exp list =
  let free_vars_case_typ = (Free.free_typ case_typ).varid in
  partition_map_using_tail (fun e es ->
    let free_vars_exp = (Free.free_typ e.note).varid in
    let free_vars_es = (Free.free_list Free.free_typ (List.map (fun exp -> exp.note) es)).varid in
    let free_vars = Free.Set.union free_vars_case_typ free_vars_es in
    map_bool_to_either e (not (Free.Set.is_empty (Free.Set.inter free_vars_exp free_vars)))
  ) exps
   
(* The following functions check that the given binds, args or type case 
 * actually have the correct matching. This is necessary for checking that 
 * the generated monomorphized instances actually follow the definition 
 * of a type family.
 *)
let check_matching (m_env : monoenv) (call_args : arg list) (match_args : arg list) = 
  Option.is_some (try match_list match_arg m_env.il_env Il.Subst.empty call_args match_args with Irred -> None)

let check_family_types_correct_matching_binds (m_env : monoenv) (subst : subst) (binds : bind list) (exp : exp) (prems : prem list): bool =
  let id_args_exp_and_prem = get_all_dep_types_in_exp (Il.Subst.subst_exp subst exp) 
      @ List.concat_map (fun prem -> (get_all_dep_types_in_prem (Il.Subst.subst_prem subst prem))) prems in
  let id_args_check id_args = 
  List.for_all (fun (id, dep_args) -> let (_params, insts) = Il.Env.find_typ m_env.il_env id in
    match insts with
      | [] -> false
      | [inst] when Mono_nat_subset.check_normal_type_creation inst -> true
      | _ -> Option.is_some (List.find_opt (fun inst -> match inst.it with | InstD (_, args, _) -> check_matching m_env dep_args args ) insts) 
  ) id_args in
  id_args_check (List.concat_map get_all_dep_types_in_bind (Il.Subst.subst_list Il.Subst.subst_bind subst binds)) && 
  id_args_check id_args_exp_and_prem

let check_family_types_correct_matching_typcase (m_env : monoenv) (subst : subst) (exp_typ_pairs : (exp * typ) list): bool =
  List.for_all (fun typ -> 
    let id_args = get_all_dep_types_in_typ typ in 
    List.for_all (fun (id, dep_args) -> let (_params, insts) = Il.Env.find_typ m_env.il_env id in
      match insts with
        | [] -> false
        | [inst] when Mono_nat_subset.check_normal_type_creation inst -> true
        | _ -> Option.is_some (List.find_opt (fun inst -> match inst.it with | InstD (_, args, _) -> check_matching m_env dep_args args ) insts) 
    ) id_args
  ) ((Il.Subst.subst_list Il.Subst.subst_typ subst (List.map snd exp_typ_pairs)))

(* HACK to resolve nat subsets - only works for variable expressions *)
let iter_get_nat_cases (m_env : monoenv): (Num.nat list) StringMap.t ref * (module Iter.Arg) = 
  let module Arg =
    struct
      include Iter.Skip
      let acc = ref StringMap.empty
      let visit_exp exp =
        match exp.it with 
          | TheE ({it = CallE (_, [ {it = ExpA ({it = VarE var_id; _}); _} ]); _}) -> 
            let typ_id = Print.string_of_typ exp.note in
            if StringMap.mem var_id.it !acc then () else 
            (match (StringMap.find_opt typ_id m_env.nat_subs_set) with
              | None -> ()
              | Some nat_list -> acc := StringMap.add var_id.it nat_list !acc
            )
          | _ -> ()
    end
  in 
  Arg.acc, (module Arg)

let rec check_recursive_type (id : id) (t : typ): bool =
  match t.it with
    | VarT (typ_id, _) -> id = typ_id
    | IterT (typ, _iter) -> check_recursive_type id typ
    | TupT exp_typ_pairs -> List.exists (fun (_, typ) -> check_recursive_type id typ) exp_typ_pairs
    | _ -> false

let rec get_all_case_instances (m_env : monoenv) (var_id : id) (concrete_args : arg list) (inst : inst): exp' list =
  match inst.it with
    | InstD (_, args, deftyp) -> 
      let subst = Option.value (try Il.Eval.match_list match_arg m_env.il_env Il.Subst.empty concrete_args args with Irred -> None) ~default:Il.Subst.empty in
      let new_deftyp = Il.Subst.subst_deftyp subst deftyp in
      match new_deftyp.it with
      | AliasT typ -> get_all_case_instances_from_typ m_env typ
      | StructT _typfields -> []
      | VariantT typcases when List.for_all (fun (_, (_, t, _), _) -> t.it = TupT []) typcases -> 
        List.map (fun (m, _, _) -> CaseE(m, empty_tuple_exp no_region)) typcases
      | VariantT typcases -> 
        List.iter (fun (_, (_, t, _), _) -> 
          if check_recursive_type var_id t then raise (UnboundedArg (Print.string_of_typ t)) else () 
        ) typcases;
        List.concat_map (fun (m, (_, t, _), _) -> 
          let case_instances = get_all_case_instances_from_typ m_env t in
          List.map (fun e -> CaseE(m, e $$ t.at % t)) case_instances
        ) typcases 

and get_all_case_instances_from_typ (m_env : monoenv) (typ: typ): exp' list  = 
  let apply_phrase t e = e $$ t.at % t in 
  match typ.it with
    | BoolT -> [BoolE false; BoolE true]
    | VarT(var_id, dep_args) -> let (_, insts) = Il.Env.find_typ m_env.il_env var_id in 
      (match insts with
        | [] -> [] (* Should never happen *)
        | [inst] when Mono_nat_subset.check_normal_type_creation inst -> get_all_case_instances m_env var_id dep_args inst
        | _ -> match List.find_opt (fun inst -> match inst.it with | InstD (_, args, _) -> check_matching m_env dep_args args) insts with
          | None -> raise (UnboundedArg (Print.string_of_typ typ))
          | Some inst -> get_all_case_instances m_env var_id dep_args inst
      )
    | TupT exp_typ_pairs -> let instances_list = List.map (fun (_, t) -> List.map (apply_phrase t) (get_all_case_instances_from_typ m_env t)) exp_typ_pairs in
      List.map (fun exps -> TupE exps) (product_of_lists_append instances_list)
    | IterT (t, Opt) -> 
      let instances = get_all_case_instances_from_typ m_env t in
      OptE None :: List.map (fun e -> OptE (Some (apply_phrase t e))) instances
    (* | _ -> print_endline ("Encountered invalid type " ^ string_of_typ typ); [] *)
    | _ -> raise (UnboundedArg (Print.string_of_typ typ))

let get_concrete_matches_rule (m_env : monoenv) (_at : region) (rule : rule) (cases : (Num.nat list) StringMap.t) (bind : bind): (id * exp) list = 
  match bind.it with
    | ExpB (var_id, typ) -> 
      (match (StringMap.find_opt var_id.it cases) with
       | Some nat_list -> List.map (fun n -> (var_id, NumE (`Nat n) $$ typ.at % (NumT `NatT $ typ.at))) nat_list
       | None -> 
          let case_instances = try get_all_case_instances_from_typ m_env typ with
            | UnboundedArg msg -> print_endline ("WARNING: " ^ msg_prefix ^ msg);
              print_endline ("For type: " ^ string_of_typ typ);
              print_endline ("For rule: " ^ Print.string_of_rule rule); 
              []
              (* _unbounded_error _at msg *)
          in
          List.map (fun e -> (var_id, e $$ typ.at % typ)) case_instances)
    | _ -> []
  
let get_concrete_matches_clause (m_env : monoenv) (_at : region) (id : id) (clause : clause) (cases : (Num.nat list) StringMap.t) (bind : bind): (id * exp) list = 
  match bind.it with
    | ExpB (var_id, typ) -> 
      (match (StringMap.find_opt var_id.it cases) with
       | Some nat_list -> List.map (fun n -> (var_id, NumE (`Nat n) $$ typ.at % (NumT `NatT $ typ.at))) nat_list
       | None -> 
          let case_instances = try get_all_case_instances_from_typ m_env typ with
            | UnboundedArg msg -> print_endline ("WARNING: " ^ msg_prefix ^ msg);
              print_endline ("For type: " ^ string_of_typ typ); 
              print_endline ("For clause: " ^ Print.string_of_clause id clause); 
              []
              (* _unbounded_error _at msg *)
          in
          List.map (fun e -> (var_id, e $$ typ.at % typ)) case_instances)
    | _ -> []

(* Monomorphization Pass *)

let rec transform_exp (m_env : monoenv) (subst : subst) (exp : exp): exp =
  let t_func = transform_exp m_env subst in
  (match exp.it with
    | UnE (unop, optyp, e) -> UnE (unop, optyp, t_func e)
    | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2)
    | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2)
    | TupE exps -> TupE (List.map t_func exps)
    | ProjE (e, i) -> ProjE (t_func e, i)
    | CaseE (m, e) -> 
      let tups = match e.it with
        | TupE exps -> exps
        | _ -> []
      in
      let exps = List.map t_func tups in
      let id = string_of_typ_name exp.note $ no_region in
      let (_, insts) = Il.Env.find_typ m_env.il_env id in  
      let (c_args_used, c_unused_args) = split_used_types_in_type_creation m_env m insts exps exp.at in
      if c_args_used = [] 
        then CaseE (m, t_func e) 
        else CaseE (transform_mixop m_env m (List.length c_unused_args) (List.map (Il.Subst.subst_exp subst) c_args_used), TupE (c_unused_args) $$ e.at % e.note)
    | UncaseE (e, m) -> UncaseE (t_func e, m)
    | OptE (Some e) -> OptE (Some (t_func e))
    | TheE e -> TheE (t_func e)
    | StrE expfields -> StrE (map_snd t_func expfields)
    | DotE (e, a) -> DotE (t_func e, a)
    | CompE (e1, e2) -> CompE (t_func e1, t_func e2)
    | ListE exps -> ListE (List.map t_func exps)
    | LiftE e -> LiftE (t_func e)
    | MemE (e1, e2) -> MemE (t_func e1, t_func e2)
    | LenE e -> LenE (t_func e)
    | CatE (e1, e2) -> CatE (t_func e1, t_func e2)
    | IdxE (e1, e2) -> IdxE (t_func e1, t_func e2)
    | SliceE (e1, e2, e3) -> SliceE (t_func e1, t_func e2, t_func e3)
    | UpdE (e1, path, e2) -> UpdE (t_func e1, transform_path m_env subst path, t_func e2)
    | ExtE (e1, path, e2) -> ExtE (t_func e1, transform_path m_env subst path, t_func e2)
    | CallE (id, args) ->
      let (params, return_type, _) = Il.Env.find_def m_env.il_env id in
      let used = split_used_types_in_params_index params (Some return_type) in      
      let (used_args, unused_args) = partition_mapi (fun a i -> map_bool_to_either a (List.mem i used)) args in
      if used_args <> [] && check_reducible_args used_args 
        then
          (let new_id = transform_id_from_args id (List.map (transform_arg m_env subst) (List.map (reduce_arg m_env.il_env) used_args)) in
          function_calls_bind m_env id.it (CallE (new_id, List.map (transform_arg m_env subst) (List.map (reduce_arg m_env.il_env) used_args)) $$ exp.at % exp.note);
          CallE (new_id, List.map (transform_arg m_env subst) unused_args))
        else
          CallE (id, List.map (transform_arg m_env subst) args)
    | IterE (e, iterexp) -> IterE (t_func e, transform_iterexp m_env subst iterexp)
    | CvtE (e, ntyp1, ntyp2) -> CvtE (t_func e, ntyp1, ntyp2)
    | SubE (e, t1, t2) -> SubE (t_func e, transform_type m_env subst t1, transform_type m_env subst t2)
    | e -> e
  ) $$ exp.at % (transform_type m_env subst exp.note)

and transform_iterexp (m_env : monoenv) (subst : subst) (iterexp : iterexp): iterexp = 
  let (iter, id_exp_pairs) = iterexp in
  (transform_iter m_env subst iter, map_snd (transform_exp m_env subst) id_exp_pairs)

and transform_iter (m_env : monoenv) (subst : subst) (iter : iter): iter =
  match iter with 
    | ListN (e, id) -> ListN(transform_exp m_env subst (Il.Subst.subst_exp subst e), id)
    | i -> i

and transform_path (m_env : monoenv) (subst : subst) (path : path): path = 
  (match path.it with
    | RootP -> RootP
    | IdxP (p, e) -> IdxP (transform_path m_env subst p, transform_exp m_env subst e)
    | SliceP (p, e1, e2) -> SliceP (transform_path m_env subst p, transform_exp m_env subst e1, transform_exp m_env subst e2)
    | DotP (p, a) -> DotP (transform_path m_env subst p, a)
  ) $$ path.at % (transform_type m_env subst path.note)

and transform_type (m_env : monoenv) (subst: subst) (typ : typ): typ = 
  let subst_typ = Il.Subst.subst_typ subst typ in 
  (match subst_typ.it with
    | VarT (id, args) when args <> [] -> 
      if check_reducible_args args 
        then (
          let reduced_args = List.map (fun arg -> reduce_arg m_env.il_env arg) args in 
          concrete_dep_types_bind m_env id.it (VarT(id, reduced_args) $ typ.at);
          VarT (transform_id_from_args id reduced_args, []) 
        )
        else (VarT (id, List.map (transform_arg m_env subst) args))
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (e, transform_type m_env subst t)) exp_typ_pairs)
    | IterT (t, iter) -> IterT (transform_type m_env subst t, transform_iter m_env subst iter)
    | t -> t
  ) $ typ.at

and transform_arg (m_env : monoenv) (subst : subst) (arg : arg) : arg =
  (match arg.it with
    | ExpA exp -> ExpA (transform_exp m_env subst exp)
    | TypA typ -> TypA (transform_type m_env subst typ)
    | _ -> arg.it) $ arg.at
  
and transform_param (m_env : monoenv) (subst : subst) (param : param) : param =
  (match param.it with 
    | ExpP (id, typ) -> ExpP (id, transform_type m_env subst typ)
    | p -> p
  ) $ param.at

and transform_bind (m_env : monoenv) (subst : subst) (bind : bind) : bind =
  (match bind.it with
    | ExpB (id, typ) -> ExpB(id, transform_type m_env subst typ)
    | b -> b) $ bind.at
    
and transform_prem (m_env : monoenv) (subst : subst) (prem : prem): prem = 
  match prem.it with
    | IfPr e -> IfPr (transform_exp m_env subst (Il.Subst.subst_exp subst e)) $ prem.at
    | RulePr (id, m, e) -> RulePr (id, m, transform_exp m_env subst (Il.Subst.subst_exp subst e)) $ prem. at
    | IterPr (p, iterexp) -> IterPr (transform_prem m_env subst p, transform_iterexp m_env subst iterexp) $ prem.at 
    | _ -> Il.Subst.subst_prem subst prem

and transform_type_case (m_env : monoenv) (subst : subst) (typc : typcase) : typcase list = 
  let (m, (bs, typ, prems), hints) = typc in
  match get_tuple_from_type typ with
    | None -> [(m, (List.map (transform_bind m_env subst) bs, transform_type m_env subst typ, List.map (transform_prem m_env subst) prems), hints)]
    | Some exp_typ_pairs -> 
      let used, unused = split_used_dependent_types_case_args exp_typ_pairs in
      let used_ids = List.map (fun (e, t) -> 
        let case_instances = try get_all_case_instances_from_typ m_env t with
          | UnboundedArg msg -> 
            print_endline ("WARNING: " ^ msg_prefix ^ msg); 
            print_endline ("For type: " ^ string_of_typ typ);
            [](*unbounded_error typ.at msg*)
        in
        let id_t = get_variable_id_safe e in
        List.map (fun exp' -> (id_t, exp' $$ t.at % t)) case_instances
      ) used in 
      let cases_list = product_of_lists used_ids in
      let subst_list = List.map (List.fold_left (fun acc (id, exp) -> Il.Subst.add_varid acc id exp) Il.Subst.empty) cases_list in
      List.filter_map (fun new_subst -> 
        let subst_union = Il.Subst.union new_subst subst in
        if (not (check_family_types_correct_matching_typcase m_env subst_union unused)) then None
        else
          let new_typ = TupT (List.map (fun (e, typ) -> (e, (transform_type m_env subst_union typ))) unused) $ typ.at in
          let new_binds = List.map (transform_bind m_env subst_union) (List.filter (fun b -> match b.it with
            | ExpB (id, _) | TypB id -> not (Il.Subst.mem_varid new_subst id)
            | _ -> false) 
          bs) in
          let new_prems = List.map (transform_prem m_env subst_union) prems in
          let new_mixop = transform_mixop m_env m (List.length unused) (List.map snd (Il.Subst.bindings_varid new_subst)) in
          Some (new_mixop, (new_binds, new_typ, new_prems), hints)
      ) subst_list

and subst_deftyp (m_env : monoenv) (subst : subst) (deftyp : deftyp): deftyp = 
  let new_deftyp = Il.Subst.subst_deftyp subst deftyp in
  (match new_deftyp.it with
    | AliasT typ -> AliasT (transform_type m_env subst typ)
    | StructT typfields -> StructT (List.map (fun (a, (bs, t, prems), hints) -> 
      (a, (bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typfields)
    | VariantT typcases -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> 
      (m, (bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typcases)
  ) $ deftyp.at

and transform_family_type_instances (m_env : monoenv) (id : id) (insts : inst list): def' list =
  match StringMap.find_opt id.it m_env.concrete_dependent_types with
    | None -> print_endline ("WARNING: type family " ^ id.it ^ " is not being used, removing it."); []
    | Some set_ref ->
      List.filter_map ( fun t ->
        let dep_args = get_dependent_type_args t in
        let inst_opt = List.find_opt (fun inst -> match inst.it with 
          | InstD (_, args, _) -> check_matching m_env dep_args args
        ) insts in
        match inst_opt with
          | None -> None
          | Some {it = InstD (_, args, deftyp); at = at; _} -> 
            let subst = Option.value (try match_list match_arg m_env.il_env Il.Subst.empty dep_args args with Irred -> None) ~default:Il.Subst.empty in
            let new_id = transform_id_from_exps m_env id (List.map snd (Il.Subst.bindings_varid subst)) in
            let new_inst = InstD ([], [], subst_deftyp m_env subst deftyp) $ at in 
            Some (TypD (new_id, [], [new_inst]))
      ) (TypSet.elements !set_ref)

let transform_type_creation (m_env : monoenv) (id : id) (inst : inst) : def' list =
  match inst.it with 
    | InstD (_, args, deftyp) -> 
      let transform_deftyp func = match args, StringMap.find_opt id.it m_env.concrete_dependent_types with
        | [], None -> (* Means its a normal type *) 
          [TypD (id, [], [InstD ([], [], func Il.Subst.empty) $ inst.at])]
        | _, None -> 
          print_endline ("WARNING: dependent type " ^ id.it ^ " is not being used, removing it.");
          [] (* Remove the dependent type as not used *)
        | _, Some set_ref ->
          List.filter_map ( fun t -> 
            let dep_args = get_dependent_type_args t in 
            let type_params = get_user_defined_type_arguments dep_args in 
            let subst = Option.value (try Il.Eval.match_list match_arg m_env.il_env Il.Subst.empty dep_args args with Irred -> None) ~default:Il.Subst.empty in
            let def' = TypD (transform_id_from_args id dep_args, [], [InstD ([], [], func subst) $ inst.at]) in
            (match type_params with
              | [] -> Some def'
              | _ -> add_to_mono_list m_env (def' $ inst.at); None
            )
          ) (TypSet.elements !set_ref)
      in
      (match deftyp.it with 
      | AliasT typ -> transform_deftyp (fun subst -> AliasT (transform_type m_env subst typ) $ deftyp.at) 
      | StructT typfields -> (
        transform_deftyp (fun subst -> StructT (List.map (fun (a, (bs, t, prems), hints) -> 
            (a, (List.map (transform_bind m_env subst) bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typfields) 
          $ deftyp.at)
      )
      | VariantT typcases -> transform_deftyp (fun subst -> VariantT (List.concat_map (transform_type_case m_env subst) typcases) $ deftyp.at)
    )

let transform_clause (m_env : monoenv) (subst : subst) (used_indices : int list) (used_call_args : arg list) (id : id) (clause : clause) : clause list =
  let bind_exists bs subst = List.filter (fun b -> match b.it with
    | ExpB (id, _) -> not (Il.Subst.mem_varid subst id)
    | TypB id -> not (Il.Subst.mem_typid subst id)
    | _ -> false) bs 
  in  
  match clause.it with
    | DefD (binds, args, exp, prems) ->
      let used_args, unused_args = partition_mapi (fun a i -> map_bool_to_either a (List.mem i used_indices)) args in
      if not (check_matching m_env used_call_args used_args) then []
      else 
        let used_subst = Option.value (try Il.Eval.match_list match_arg m_env.il_env Il.Subst.empty used_call_args used_args with Irred -> None) ~default:Il.Subst.empty in 
        let new_subst = Il.Subst.union subst used_subst in 
        let (dep_binds, normal_binds) = split_used_dependent_types_relation_binds (bind_exists binds new_subst) exp prems in 
        if dep_binds == [] 
          then ([DefD (List.map (transform_bind m_env new_subst) (bind_exists binds new_subst), 
                  List.map (transform_arg m_env new_subst) unused_args, 
                  transform_exp m_env new_subst (Il.Subst.subst_exp new_subst exp), 
                  List.map (transform_prem m_env new_subst) prems) $ clause.at])
          else 
            let cases_list = product_of_lists (List.map (get_concrete_matches_clause m_env clause.at id clause StringMap.empty) dep_binds) in
            let subst_list = List.map (List.fold_left (fun acc (id, exp) -> Il.Subst.add_varid acc id exp) Il.Subst.empty) cases_list in
            List.map (fun clause_subst -> 
              let subst_union = Il.Subst.union new_subst clause_subst in 
              DefD (List.map (transform_bind m_env subst_union) normal_binds, 
              List.map (fun arg -> transform_arg m_env subst_union (Il.Subst.subst_arg subst_union arg)) unused_args, 
              transform_exp m_env subst_union (Il.Subst.subst_exp subst_union exp), 
              List.map (transform_prem m_env subst_union) prems) $ clause.at
            ) subst_list
        
let transform_function_definitions (m_env : monoenv) (id : id) (params: param list) (return_type : typ) (clauses : clause list) (at : Util.Source.region) (is_recursive: bool): def' list =
  let used, unused = split_used_types_in_params params return_type in
  let used_indices = split_used_types_in_params_index params (Some return_type) in
  let apply_recursive def' = match is_recursive with 
    | true -> RecD [def' $ at]
    | false -> def' 
  in
  match (StringMap.find_opt id.it m_env.calls), used with
    | _, [] -> (* function has no dependent type / type parameters *) 
      let subst = Il.Subst.empty in
      [apply_recursive (DecD (id, params, transform_type m_env subst return_type, List.concat_map (transform_clause m_env subst [] [] id) clauses))]
    | None, _ -> (* function is not used *) 
    print_endline ("WARNING: function " ^ id.it ^ " is not being used, removing it.");
    []
    | Some set_ref, _ -> 
      List.filter_map (fun e -> 
        let (new_id, used_call_args) = get_function_call e in 
        let type_params = get_user_defined_type_arguments used_call_args in
        let used_param_ids = List.map get_variable_id_from_param used in 
        let subst = create_args_pairings used_param_ids used_call_args in
        let def' = DecD (new_id.it $ id.at, List.map (transform_param m_env subst) unused, 
          transform_type m_env subst return_type, 
          List.concat_map (transform_clause m_env subst used_indices used_call_args id) clauses) in 
        match type_params with
          | [] -> Some (apply_recursive def')
          | _ -> add_to_mono_list m_env ((apply_recursive def') $ at); None
        ) (ExpSet.elements !set_ref)

let transform_rule (m_env : monoenv) (rule : rule) : rule list =
  match rule.it with
    | RuleD (rule_id, binds, mixop, exp, prems) ->
      let acc_cases, (module Arg: Iter.Arg) = iter_get_nat_cases m_env in
      let module Acc = Iter.Make(Arg) in
      Acc.binds binds;
      Acc.exp exp;
      Acc.prems prems;
      let (used_deps, unused) = split_used_dependent_types_relation_binds binds exp prems in
      if used_deps == [] 
      then [RuleD(rule_id, List.map (transform_bind m_env Subst.empty) binds, mixop, transform_exp m_env Subst.empty exp, List.map (transform_prem m_env Subst.empty) prems) $ rule.at] 
      else (
        let cases_list = product_of_lists (List.map (get_concrete_matches_rule m_env rule.at rule !acc_cases) used_deps) in
        let subst_list = List.map (List.fold_left (fun acc (id, exp) -> Il.Subst.add_varid acc id exp) Il.Subst.empty) cases_list in
        List.filter_map (fun subst ->
          if (not (check_family_types_correct_matching_binds m_env subst unused exp prems)) then None else 
          let new_id = transform_id_from_exps m_env rule_id (List.map snd (Il.Subst.bindings_varid subst)) in
          let new_prems = List.map (transform_prem m_env subst) prems in
          let subst_exp = Il.Subst.subst_exp subst exp in
          Some (RuleD (new_id, List.map (transform_bind m_env subst) unused, mixop, transform_exp m_env subst subst_exp, new_prems) $ rule.at)
        ) subst_list)

let rec _transform_def (m_env : monoenv) (def : def) : def list =
  (match def.it with
    | TypD (id, _, [inst]) when Mono_nat_subset.check_normal_type_creation inst -> transform_type_creation m_env id inst
    | TypD (id, _params, insts) -> transform_family_type_instances m_env id insts
    | RelD (id, mixop, typ, rules) -> 
      [RelD (id, mixop, typ, List.concat_map (transform_rule m_env) rules)]
    | RecD [{ it = DecD (id, params, typ, clauses); _}] -> transform_function_definitions m_env id params typ clauses def.at true
    | DecD (id, params, typ, clauses) -> transform_function_definitions m_env id params typ clauses def.at false
    | RecD defs -> let new_defs = List.concat_map (_transform_def m_env) defs in
      (match new_defs with
        | [] -> []
        | _ -> [RecD new_defs]
      )
    | _ -> [def.it]) |> List.map (fun new_def -> new_def $ def.at) 

let _reorder_monomorphized_functions (m_env : monoenv) (def : def): def list =
  let rec get_ids d = (match d.it with
      | TypD (id, _, _) -> [id.it]
      | RelD (id, _, _, _) -> [id.it]
      | DecD (id, _, _, _) -> [id.it]
      | RecD defs -> List.concat_map get_ids defs
      | _ -> []
    ) in
  
  let partition_list mono_list def = 
    let free_def_vars = Free.free_def def in
    List.partition (fun d -> 
      let ids = Free.Set.of_list (get_ids d) in
      let typs = Free.Set.is_empty (Free.Set.inter ids free_def_vars.typid) in
      let funcs = Free.Set.is_empty (Free.Set.inter ids free_def_vars.defid) in
      typs && funcs
    ) mono_list in

  let (rest, filtered_mono_list) = partition_list m_env.mono_list def in
  m_env.mono_list <- rest;
  filtered_mono_list @ [def]

let rec repeat_reordering (m_env : monoenv) (defs : def list) : def list =
  match (m_env.mono_list) with
    | [] -> defs
    | _ -> repeat_reordering m_env (List.concat_map (_reorder_monomorphized_functions m_env) defs)

(* Main transformation function *)
let transform (script: Il.Ast.script) =
  let m_env = new_env in 
  let mono_sub_pass, pass_env = Mono_nat_subset.transform script in
  m_env.il_env <- Il.Env.env_of_script mono_sub_pass;
  m_env.nat_subs_set <- pass_env.nat_subs_set;
  (* Reverse the script in order to monomorphize nested ones correctly *)
  let transformed_script = List.rev (List.concat_map (_transform_def m_env) (List.rev mono_sub_pass)) in
  print_env m_env;
  repeat_reordering m_env transformed_script