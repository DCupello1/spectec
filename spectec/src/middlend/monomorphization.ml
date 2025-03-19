(* TODO - Make sure we are applying the right regions at the right spots (necessary for debugging later) *)
(* TODO - Improve eval reduction function to reduce function calls correctly (can't have function calls with irreducible arguments actually be reduced) *)
(* TODO - Fix issue with invalid recursion *)

open Il.Ast
open Il.Print

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
  mutable mono_funcs_map: ((def * int) option ref) StringMap.t;
}

let new_env() = 
{
  calls = StringMap.empty;
  concrete_dependent_types = StringMap.empty;
  il_env = Il.Env.empty;
  mono_funcs_map = StringMap.empty;
}

let mono = "Monomorphization"

let empty_tuple_exp at = TupE [] $$ at % (TupT [] $ at)

let _map_fst f = List.map (fun (v1, v2) -> (f v1, v2))

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
  
  print_endline "Mono funcs and types with type params:";
  StringMap.iter (fun id def ->
    let (def_str, _i) = match !def with
      | Some (d, i) -> (string_of_def d, i)
      | None -> ("", 0) in
    print_endline ("type param : " ^ id ^ " for definition: ");
    print_endline def_str
  ) m_env.mono_funcs_map

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

let bind_mono_func_map (m_env : monoenv) (type_params : string list) (def : def): unit =
  List.iter ( fun id ->
    match StringMap.find_opt id m_env.mono_funcs_map with
      | Some ref -> ref := Option.map (fun (d, i) -> (d, i + 1)) !ref
      | None -> m_env.mono_funcs_map <- StringMap.add id (ref (Some (def, 1))) m_env.mono_funcs_map 
  ) type_params
      
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
  
(* Computes the cartesian product of a given list. *)
let product_of_lists (lists : 'a list list) = 
  List.fold_left (fun acc seq ->
    List.concat_map (fun existing -> 
      List.map (fun v -> v :: existing) seq) acc) [[]] lists

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
    | TupE exps -> "t" ^ String.concat "_" (List.map to_string_exp exps) 
    | CaseE (mixop, {it = TupE []; _}) -> to_string_mixop mixop 
    | CaseE (mixop, exp) -> to_string_mixop mixop ^ "_" ^ to_string_exp exp
    | CvtE (e, _, _) -> to_string_exp e
    | SubE (e, _, _) -> to_string_exp e
    | _ -> error exp.at mono ("Cannot transform " ^ string_of_exp exp ^ " into string")

and to_string_typ (typ : typ) : string = 
  match typ.it with
    | BoolT | NumT _ | TextT -> string_of_typ typ
    | VarT (id, args) -> id.it ^ "_" ^ String.concat "__" (List.map to_string_arg args)
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
  id.it ^ "_mono_" ^ String.concat "__" (List.map to_string_arg args) $ id.at

and transform_string (text : string) (strs : string list): string =
  if strs = [] then text else 
  text ^ "_mono_" ^ (String.concat "__" strs)
and transform_id_from_exps (id : id) (exps : exp list): id =
  transform_string id.it (List.map to_string_exp exps) $ id.at

(* TODO fix this to remove the correct holes in the more complicated case *)
and transform_mixop (m : mixop) (num_kept : int) (strs : string list) : mixop =
  if strs = [] then m else
  match m with
    | [{it = Atom.Atom a; _} as atom]::tail when List.for_all ((=) []) tail -> 
      [Atom.Atom (transform_string a strs) $$ atom.at % atom.note]::(List.init num_kept (fun _ -> []))
    | _ -> 
      let rec aux num_empty = function
        | [] -> []
        | [] :: ls when num_empty > num_kept -> aux (num_empty + 1) ls
        | [] :: ls -> [] :: aux (num_empty + 1) ls
        | _ :: ls -> aux num_empty ls
      in
      List.mapi (fun i atoms -> 
      let length_last = List.length m in 
      let new_atom = Atom.Atom (transform_string "" strs) $$ (no_region, Atom.info "") in
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
    | _ -> false

and check_reducible_arg (arg: arg): bool =
  match arg.it with
    | TypA _ -> true
    | ExpA exp -> check_reducible_exp exp
    | _ -> false

and check_reducible_args (args: arg list): bool =
  List.for_all check_reducible_arg args

(* Simple getters which traverse part of the AST *)
(* TODO Improve traversal, doesn't need to traverse this much maybe.
Either that or separate to a different file.
*)

let get_dependent_type_args (typ : typ): arg list = 
  match typ.it with  
    | VarT (_, concrete_args) -> concrete_args
    | _ -> error typ.at mono "Applied monomorphization on a non-concrete dependent type"

let get_function_call (exp : exp): id * arg list =
  match exp.it with
    | CallE (id, args) -> (id, args)
    | _ -> error exp.at mono "Applied monomorphization on a non-function call expression"

let get_variable_from_typ (typ : typ): id * arg list =
  match typ.it with
    | VarT (id, args) -> (id, args)
    | _ -> error typ.at mono "Case expression should have variable type" 
  
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
  
let get_tuple_exp (exp : exp): exp list =
  match exp.it with
    | TupE es -> es
    | _ -> []
  
let rec get_all_variable_ids_arg (arg : arg): string list = 
  match arg.it with
    | ExpA exp -> get_all_variable_ids_exp exp
    | TypA typ -> get_all_variable_ids_typ typ
    | _ -> []

and get_all_variable_ids_exp (exp : exp): string list = 
  match exp.it with
    | VarE id -> [id.it]
    | CaseE (_, e) -> get_all_variable_ids_exp e
    | CallE (_, args) -> List.concat_map get_all_variable_ids_arg args
    | SubE (e, _, _) -> get_all_variable_ids_exp e
    | TupE exps -> List.concat_map get_all_variable_ids_exp exps
    | _ -> []

and get_all_variable_ids_typ (typ : typ): string list =
  match typ.it with
    | VarT (_, args) -> List.concat_map get_all_variable_ids_arg args
    | IterT (t, _) -> get_all_variable_ids_typ t
    | TupT exp_typ_pairs -> List.concat_map (fun (_, t) -> get_all_variable_ids_typ t) exp_typ_pairs
    | _ -> []

and get_all_variable_ids_bind (bind : bind): string list =
  match bind.it with
    | ExpB (_, typ) -> get_all_variable_ids_typ typ
    | _ -> []

and get_all_variable_ids_param (param : param): string list =
  match param.it with
    | ExpP (_, typ) -> get_all_variable_ids_typ typ
    | _ -> []

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
    | ExpA _ -> [] (* TODO expand later to exps *)
    | TypA typ -> get_all_dep_types_in_typ typ
    | _ -> []
and get_all_dep_types_in_bind (bind : bind): (id * arg list) list = 
  match bind.it with
    | ExpB (_, typ) -> get_all_dep_types_in_typ typ
    | _ -> []
    
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

(* Gets type information specified by a tranformation function, specifically in call exps and case exps *)
let rec get_type_info_from_exp (transform_func : typ -> 'b list) (exp : exp): 'b list =
  let r_func = get_type_info_from_exp
 transform_func in
  match exp.it with
    | CaseE (_, e) -> List.concat_map (fun e -> transform_func e.note) (get_tuple_exp e) @ r_func e
    | CallE (_, args) -> transform_func exp.note @ List.concat_map (get_type_info_from_arg transform_func) args
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
    | UpdE (e1, p, e2) | ExtE (e1, p, e2) -> r_func e1 @ get_type_info_from_path transform_func p @ r_func e2
    | IterE (e1, (_, id_exp_pairs)) -> r_func e1 @ List.concat_map (fun (_, e) -> r_func e) id_exp_pairs
    | CvtE (e1, _, _) | SubE (e1, _, _) -> r_func e1 
    | _ -> []

and get_type_info_from_path (transform_func : typ -> 'b list) (path : path): 'b list = 
  match path.it with
    | RootP -> []
    | IdxP (p, e) -> get_type_info_from_path transform_func p @ get_type_info_from_exp
   transform_func e
    | SliceP (p, e1, e2) -> get_type_info_from_path transform_func p @ get_type_info_from_exp
   transform_func e1 @ get_type_info_from_exp
   transform_func e2
    | DotP (p, _) -> get_type_info_from_path transform_func p

and get_type_info_from_typ (transform_func : typ -> 'b list) (typ : typ): 'b list =
  match typ.it with
    | VarT (_id, args) -> List.concat_map (get_type_info_from_arg transform_func) args
    | TupT exp_typ_pairs -> List.concat_map (fun (e, t) -> get_type_info_from_exp
   transform_func e @ get_type_info_from_typ transform_func t) exp_typ_pairs
    | IterT (t, _) -> get_type_info_from_typ transform_func t
    | _ -> []

and get_type_info_from_arg (transform_func : typ -> 'b list) (arg : arg): 'b list =
  match arg.it with 
    | ExpA e -> get_type_info_from_exp
   transform_func e
    | TypA t -> get_type_info_from_typ transform_func t
    | _ -> []
  
and get_type_info_from_prem (transform_func : typ -> 'b list) (prem : prem): 'b list = 
  match prem.it with
    | RulePr (_, _, e) -> get_type_info_from_exp
   transform_func e
    | IfPr e -> get_type_info_from_exp
   transform_func e
    | LetPr (e1, e2, _) -> get_type_info_from_exp
   transform_func e1 @ get_type_info_from_exp
   transform_func e2
    | ElsePr -> []
    | IterPr (p, (_, id_exp_pairs)) -> get_type_info_from_prem transform_func p @ List.concat_map (fun (_, e) -> get_type_info_from_exp
   transform_func e) id_exp_pairs

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

(* Hack for now until there is a way to distinguish family types well *)
let check_normal_type_creation (inst : inst) : bool = 
  match inst.it with
    | InstD (_, args, _) -> List.for_all (fun arg -> 
      match arg.it with 
        | ExpA {it = VarE _; _} | TypA _ -> true
        | _ -> false  
    ) args 

(* TODO Improve these check functions to traverse and look into function call return types *)
let check_used_dependent_types_case_args (exp_typ_pairs : (exp * typ) list): (exp * typ) list * (exp * typ) list =
  partition_map_using_tail (fun ((_, t) as p) ps -> 
    let id_t = match t.it with
        | VarT (id, _) -> id.it
        | _ -> ""
    in 
    map_bool_to_either p (List.mem id_t (List.concat_map (fun (_, t) -> get_all_variable_ids_typ t) (List.filter (fun (_, t) -> check_dep_type t) ps)))
  ) exp_typ_pairs

let check_used_dependent_types_case_args_index (exp_typ_pairs : (exp * typ) list): int list =
  filter_map_using_taili (fun (_, t) ps i -> 
    let id_t = match t.it with
        | VarT (id, _) -> id.it
        | _ -> ""
    in 
    map_bool_to_option i (List.mem id_t (List.concat_map (fun (_, t) -> get_all_variable_ids_typ t) (List.filter (fun (_, t) -> check_dep_type t) ps)))
  ) exp_typ_pairs

let check_used_dependent_types_relation_binds (binds : bind list) (exp : exp) (prems: prem list): bind list * bind list =
  
  let dep_ids_in_relation = get_type_info_from_exp
 get_all_variable_ids_typ exp @ List.concat_map (get_type_info_from_prem get_all_variable_ids_typ) prems in
  partition_map_using_tail (fun b bs ->
    match b.it with
      | ExpB (id, _) -> 
        let dep_ids_in_binds = List.concat_map get_all_variable_ids_bind (List.filter check_dep_typ_in_bind bs) in
        map_bool_to_either b (List.mem id.it (dep_ids_in_binds @ dep_ids_in_relation))
      | _ -> Right b 
  ) binds
      
let check_used_types_in_params (params : param list) (return_type : typ): param list * param list = 
  partition_map_using_tail (fun p ps -> 
    let is_type_param, id_p = match p.it with
        | ExpP (id, _) -> false, id.it
        | TypP id -> true, id.it
        | _ -> false, ""
    in
    let variable_ids = (List.concat_map get_all_variable_ids_param (List.filter check_dep_typ_in_params ps)) in
    map_bool_to_either p (is_type_param || List.mem id_p (variable_ids @ (get_all_variable_ids_typ return_type)))
  ) params

let check_used_types_in_params_index (params : param list) (return_type : typ option): int list = 
  filter_map_using_taili (fun p ps i ->
    let is_type_param, id_p = match p.it with
      | ExpP (id, _) -> false, id.it
      | TypP id -> true, id.it
      | _ -> false, ""
    in
    let return_typ_ids = match return_type with
      | None -> []
      | Some typ -> get_all_variable_ids_typ typ 
    in
    let variable_ids = (List.concat_map get_all_variable_ids_param (List.filter check_dep_typ_in_params ps)) in
    map_bool_to_option i (is_type_param || List.mem id_p (variable_ids @ return_typ_ids))
  ) params

let check_used_types_in_type_creation (m_env : monoenv) (mixop : mixop) (insts: inst list) (exps : exp list) (at: Util.Source.region): exp list * exp list =
  if exps = [] then ([], []) else
  match insts with
    | [inst] when check_normal_type_creation inst -> 
      let (_, (_, t, _), _) = get_case_instance m_env mixop at inst in
      (match (get_tuple_from_type t) with 
        | None -> ([], [])
        | Some exp_typ_pairs -> 
          let used_indices = check_used_dependent_types_case_args_index exp_typ_pairs in
          partition_mapi (fun e i -> map_bool_to_either e (List.mem i used_indices)) exps
      )
    | _ -> ([], [])

let check_matching (m_env : monoenv) (call_args : arg list) (match_args : arg list) = 
  Option.is_some (try match_list match_arg m_env.il_env Il.Subst.empty call_args match_args with Irred -> None)

let check_family_types_correct_matching_binds (m_env : monoenv) (subst : subst) (binds : bind list) (exp : exp) (prems : prem list): bool =
  let id_args_exp_and_prem = get_type_info_from_exp get_all_dep_types_in_typ (Il.Subst.subst_exp subst exp) 
      @ List.concat_map (fun prem -> (get_type_info_from_prem get_all_dep_types_in_typ (Il.Subst.subst_prem subst prem))) prems in
  let id_args_check id_args = 
  List.for_all (fun (id, dep_args) -> let (_params, insts) = Il.Env.find_typ m_env.il_env id in
    match insts with
      | [] -> false
      | [inst] when check_normal_type_creation inst -> true
      | _ -> Option.is_some (List.find_opt (fun inst -> match inst.it with | InstD (_, args, _) -> check_matching m_env dep_args args ) insts) 
  ) id_args in
  id_args_check (List.concat_map get_all_dep_types_in_bind (fst (Il.Subst.subst_binds subst binds))) && 
  id_args_check id_args_exp_and_prem


let check_family_types_correct_matching_typcase (m_env : monoenv) (subst : subst) (exp_typ_pairs : (exp * typ) list): bool =
  List.for_all (fun typ -> 
    let id_args = get_all_dep_types_in_typ typ in 
    List.for_all (fun (id, dep_args) -> let (_params, insts) = Il.Env.find_typ m_env.il_env id in
      match insts with
        | [] -> false
        | [inst] when check_normal_type_creation inst -> true
        | _ -> Option.is_some (List.find_opt (fun inst -> match inst.it with | InstD (_, args, _) -> check_matching m_env dep_args args ) insts) 
    ) id_args
  ) ((Il.Subst.subst_list Il.Subst.subst_typ subst (List.map snd exp_typ_pairs)))


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
      let exps = List.map t_func (get_tuple_exp e) in
      let (id, _) = get_variable_from_typ exp.note in
      let (_, insts) = Il.Env.find_typ m_env.il_env id in  
      let (c_args_used, c_unused_args) = check_used_types_in_type_creation m_env m insts exps exp.at in
      if c_args_used = [] 
        then CaseE (m, t_func e) 
        else CaseE (transform_mixop m (List.length c_unused_args) (List.map to_string_exp c_args_used), TupE (c_unused_args) $$ e.at % e.note)
    | UncaseE (e, m) -> UncaseE (t_func e, m)
    | OptE (Some e) -> OptE (Some (t_func e))
    | TheE e -> TheE (t_func e)
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
      let args' = List.map (Il.Eval.reduce_arg m_env.il_env) args in
      let (params, return_type, _) = Il.Env.find_def m_env.il_env id in
      let used = check_used_types_in_params_index params (Some return_type) in      
      let (used_args, unused_args) = partition_mapi (fun a i -> map_bool_to_either a (List.mem i used)) args' in
      if used_args <> [] && check_reducible_args used_args 
        then
          (let new_id = transform_id_from_args id used_args in
          function_calls_bind m_env id.it (CallE (new_id, List.map (transform_arg m_env subst) used_args) $$ exp.at % exp.note);
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
  (iter, map_snd (transform_exp m_env subst) id_exp_pairs)

and transform_path (m_env : monoenv) (subst : subst) (path : path): path = 
  (match path.it with
    | RootP -> RootP
    | IdxP (p, e) -> IdxP (transform_path m_env subst p, transform_exp m_env subst e)
    | SliceP (p, e1, e2) -> SliceP (transform_path m_env subst p, transform_exp m_env subst e1, transform_exp m_env subst e2)
    | DotP (p, a) -> DotP (transform_path m_env subst p, a)
  ) $$ path.at % (transform_type m_env subst path.note)

and transform_type (m_env : monoenv) (subst: subst) (typ : typ): typ = 
  let reduced_typ = Il.Eval.reduce_typ m_env.il_env (Il.Subst.subst_typ subst typ) in
  (match reduced_typ.it with
    | VarT (id, args) when args <> [] -> 
      if check_reducible_args args 
        then (
          concrete_dep_types_bind m_env id.it (VarT(id, args) $ typ.at); 
          VarT (transform_id_from_args id args, []) 
        )
        else typ.it
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (e, transform_type m_env subst t)) exp_typ_pairs)
    | IterT (t, iter) -> IterT (transform_type m_env subst t, iter)
    | t -> t
  ) $ typ.at

and transform_arg (m_env : monoenv) (subst : subst) (arg : arg) : arg =
  (match arg.it with
    | ExpA exp -> ExpA (transform_exp m_env subst exp)
    | TypA typ -> TypA (transform_type m_env subst typ)
    | _ -> arg.it) $ arg.at
  
and transfrom_param (m_env : monoenv) (subst : subst) (param : param) : param =
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
    | IterPr (p, iterexp) -> IterPr (transform_prem m_env subst p, iterexp) $ prem.at 
    | _ -> Il.Subst.subst_prem subst prem

let subst_deftyp (m_env : monoenv) (subst : subst) (deftyp : deftyp): deftyp = 
  let new_deftyp = Il.Subst.subst_deftyp subst deftyp in
  (match new_deftyp.it with
    | AliasT typ -> AliasT (transform_type m_env subst typ)
    | StructT typfields -> StructT (List.map (fun (a, (bs, t, prems), hints) -> 
      (a, (bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typfields)
    | VariantT typcases -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> 
      (m, (bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typcases)
  ) $ deftyp.at

  
let rec get_all_case_instances (m_env : monoenv) (concrete_args : arg list) (inst : inst): exp' list =
  match inst.it with
    | InstD (_, args, deftyp) -> 
      let subst = Option.value (try Il.Eval.match_list match_arg m_env.il_env Il.Subst.empty concrete_args args with Irred -> None) ~default:Il.Subst.empty in
      let new_deftyp = subst_deftyp m_env subst deftyp in
      match new_deftyp.it with
      | AliasT typ -> get_all_case_instances_from_typ m_env typ
      | StructT _typfields -> []
      | VariantT typcases when List.for_all (fun (_, (_, t, _), _) -> t.it = TupT []) typcases -> 
        List.map (fun (m, _, _) -> CaseE(m, empty_tuple_exp no_region)) typcases
      | VariantT typcases -> let mono_cases = List.concat_map (transform_type_case m_env subst) typcases in
        List.concat_map (fun (m, (_, t, _), _) -> 
          let case_instances = get_all_case_instances_from_typ m_env t in
          List.map (fun e -> CaseE(m, e $$ t.at % t)) case_instances
        ) mono_cases

and get_all_case_instances_from_typ (m_env : monoenv) (typ: typ): exp' list  = 
  let apply_phrase e = e $$ typ.at % typ in 
  match typ.it with
    | BoolT -> [BoolE false; BoolE true]
    | VarT(var_id, dep_args) -> let (_, insts) = Il.Env.find_typ m_env.il_env var_id in 
      (match insts with
        | [] -> [] (* Should never happen *)
        | [inst] when check_normal_type_creation inst -> get_all_case_instances m_env dep_args inst
        | _ -> match List.find_opt (fun inst -> match inst.it with | InstD (_, args, _) -> check_matching m_env dep_args args) insts with
          | None -> [] (* TODO maybe raise error here since this shouldn't happen *)
          | Some inst -> get_all_case_instances m_env dep_args inst
      )
    | TupT exp_typ_pairs -> let instances_list = List.map (fun (_, t) -> get_all_case_instances_from_typ m_env t) exp_typ_pairs in
      List.map (fun exps' -> TupE (List.map apply_phrase exps')) (product_of_lists instances_list)
    | IterT (typ, Opt) -> 
      let instances = get_all_case_instances_from_typ m_env typ in
      OptE None :: List.map (fun e -> OptE (Some (apply_phrase e))) instances
    (* | _ -> print_endline ("Encountered invalid type " ^ string_of_typ typ); [] *)
    | _ -> raise (UnboundedArg (string_of_typ typ))

and transform_type_case (m_env : monoenv) (subst : subst) (typc : typcase) : typcase list = 
  let (m, (bs, typ, prems), hints) = typc in
  match get_tuple_from_type typ with
    | None -> [(m, (List.map (transform_bind m_env subst) bs, transform_type m_env subst typ, List.map (transform_prem m_env subst) prems), hints)]
    | Some exp_typ_pairs -> 
      let used, unused = check_used_dependent_types_case_args exp_typ_pairs in
      let used_ids = List.map (fun (e, t) -> 
        let case_instances = try get_all_case_instances_from_typ m_env t with
          | UnboundedArg msg -> print_endline ("WARNING: " ^ msg_prefix ^ msg); [](*unbounded_error typ.at msg*)
        in
        let id_t = get_variable_id_safe e in
        List.map (fun exp -> (id_t, exp $$ t.at % t)) case_instances
      ) used in
      let cases_list = product_of_lists used_ids in
      let subst_list = List.map (List.fold_left (fun acc (id, exp) -> Il.Subst.add_varid acc id exp) Il.Subst.empty) cases_list in
      List.filter_map (fun new_subst -> 
        let subst_union = Il.Subst.union new_subst subst in
        if (not (check_family_types_correct_matching_typcase m_env subst_union unused)) then None else
        let new_typ = TupT (List.map (fun (e, typ) -> (e, (transform_type m_env subst_union typ))) unused) $ typ.at in
        let new_binds = List.map (transform_bind m_env subst_union) (List.filter (fun b -> match b.it with
          | ExpB (id, _) | TypB id -> not (Il.Subst.mem_varid new_subst id)
          | _ -> false) 
        bs) in
        let new_prems = List.map (transform_prem m_env subst_union) prems in
        let new_mixop = transform_mixop m (List.length unused) (List.map (fun (_, e) -> to_string_exp e) (Il.Subst.bindings_varid new_subst)) in
        Some (new_mixop, (new_binds, new_typ, new_prems), hints)
      ) subst_list

and transform_family_type_instances (m_env : monoenv) (id : id) (insts : inst list): def' list =
  match StringMap.find_opt id.it m_env.concrete_dependent_types with
    | None -> [] (* Type family not used *)
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
            let new_id = transform_id_from_exps id (List.map snd (Il.Subst.bindings_varid subst)) in
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
              | _ -> bind_mono_func_map m_env type_params (def' $ inst.at); None
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

let get_concrete_matches (m_env : monoenv) (_at : region) (bind : bind): (id * exp) list = 
  match bind.it with
    | ExpB (var_id, typ) -> 
      let case_instances = try get_all_case_instances_from_typ m_env typ with
        | UnboundedArg msg -> print_endline ("WARNING: " ^ msg_prefix ^ msg); [](*_unbounded_error at msg*)
      in
      List.map (fun e -> (var_id, e $$ typ.at % typ)) case_instances
    | _ -> []

let transform_clause (m_env : monoenv) (subst : subst) (used_indices : int list) (used_call_args : arg list) (clause : clause) : clause option =
  let bind_exists bs subst = List.filter (fun b -> match b.it with
    | ExpB (id, _) -> not (Il.Subst.mem_varid subst id)
    | TypB id -> not (Il.Subst.mem_typid subst id)
    | _ -> false) bs 
  in  
  match clause.it with
    | DefD (binds, args, exp, prems) ->
      let used_args, unused_args = partition_mapi (fun a i -> map_bool_to_either a (List.mem i used_indices)) args in
      if not (check_matching m_env used_call_args used_args) then None
      else 
        let used_subst = Option.value (try Il.Eval.match_list match_arg m_env.il_env Il.Subst.empty used_call_args used_args with Irred -> None) ~default:Il.Subst.empty in 
        let new_subst = Il.Subst.union subst used_subst in 
        Some (DefD (List.map (transform_bind m_env new_subst) (bind_exists binds new_subst), 
        List.map (transform_arg m_env new_subst) unused_args, 
        transform_exp m_env new_subst (Il.Subst.subst_exp new_subst exp), 
        List.map (transform_prem m_env new_subst) prems) $ clause.at)

let transform_function_definitions (m_env : monoenv) (id : id) (params: param list) (return_type : typ) (clauses : clause list) (at : Util.Source.region) (is_recursive: bool): def' list =
  let used, unused = check_used_types_in_params params return_type in
  let used_indices = check_used_types_in_params_index params (Some return_type) in
  let apply_recursive def' = match is_recursive with 
    | true -> RecD [def' $ at]
    | false -> def' 
  in
  match (StringMap.find_opt id.it m_env.calls), used with
    | _, [] -> (* function has no dependent type / type parameters *) 
      let subst = Il.Subst.empty in
      [apply_recursive (DecD (id, params, transform_type m_env subst return_type, List.filter_map (transform_clause m_env subst [] []) clauses))]
    | None, _ -> (* function is not used *) 
    print_endline ("WARNING: function " ^ id.it ^ " is not being used, removing it.");
    []
    | Some set_ref, _ -> 
      List.filter_map ( fun e -> 
        let (new_id, used_call_args) = get_function_call e in 
        let type_params = get_user_defined_type_arguments used_call_args in
        let used_param_ids = List.map get_variable_id_from_param used in 
        let subst = create_args_pairings used_param_ids used_call_args in
        let def' = DecD (new_id.it $ id.at, List.map (transfrom_param m_env subst) unused, 
          transform_type m_env subst return_type, 
          List.filter_map (transform_clause m_env subst used_indices used_call_args) clauses) in 
        match type_params with
          | [] -> Some (apply_recursive def')
          | _ -> bind_mono_func_map m_env type_params ((apply_recursive def') $ at); None
        ) (ExpSet.elements !set_ref)

let transform_rule (m_env : monoenv) (rule : rule) : rule list =
  match rule.it with
    | RuleD (rule_id, binds, mixop, exp, prems) ->
      let (used_deps, unused) = check_used_dependent_types_relation_binds binds exp prems in
      let cases_list = product_of_lists (List.map (get_concrete_matches m_env rule.at) used_deps) in
      let subst_list = List.map (List.fold_left (fun acc (id, exp) -> Il.Subst.add_varid acc id exp) Il.Subst.empty) cases_list in
      List.filter_map (fun subst ->
        if (not (check_family_types_correct_matching_binds m_env subst unused exp prems)) then None else 
        let new_id = transform_id_from_exps rule_id (List.map snd (Il.Subst.bindings_varid subst)) in
        let new_prems = List.map (transform_prem m_env subst) prems in
        let subst_exp = Il.Subst.subst_exp subst exp in
        Some (RuleD (new_id, List.map (transform_bind m_env subst) unused, mixop, transform_exp m_env subst subst_exp, new_prems) $ rule.at)
      ) subst_list

let rec transform_def (m_env : monoenv) (def : def) : def list =
  (match def.it with
    | TypD (id, _, [inst]) when check_normal_type_creation inst -> transform_type_creation m_env id inst
    | TypD (id, _params, insts) -> transform_family_type_instances m_env id insts
    | RelD (id, mixop, typ, rules) -> 
      [RelD (id, mixop, typ, List.concat_map (transform_rule m_env) rules)]
    | RecD [{ it = DecD (id, params, typ, clauses); _}] -> transform_function_definitions m_env id params typ clauses def.at true
    | DecD (id, params, typ, clauses) -> transform_function_definitions m_env id params typ clauses def.at false
    | RecD defs -> let new_defs = List.concat_map (transform_def m_env) defs in
      (match new_defs with
        | [] -> []
        | _ -> [RecD new_defs]
      )
    | _ -> [def.it]) |> List.map (fun new_def -> new_def $ def.at) 

let rec reorder_monomorphized_functions (m_env : monoenv) (def : def): def list =
  let update_ref ref = 
    match !ref with
      | Some (d, i) -> if (i = 1) 
          then (ref := None; [def; d])
          else (ref := Some (d, i - 1); [def])
      | None -> [def]
  in
  match def.it with
    | TypD (id, _, _) -> (match StringMap.find_opt id.it m_env.mono_funcs_map with
      | Some ref -> update_ref ref
      | None -> [def]
    )
    | RecD defs -> [RecD (List.concat_map (reorder_monomorphized_functions m_env) defs) $ def.at]
    | _ -> [def]

(* Main transformation function *)
let transform (script: Il.Ast.script) =
  let m_env = new_env() in 
  m_env.il_env <- Il.Env.env_of_script script;
  (* Reverse the script in order to monomorphize nested ones correctly *)
  let transformed_script = List.rev (List.concat_map (transform_def m_env) (List.rev script)) in
  print_env m_env;
  List.concat_map (reorder_monomorphized_functions m_env) transformed_script
