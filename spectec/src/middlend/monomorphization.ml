


(* 
Step 1: Grab all concrete calls (i.e. in function calls $func(32) or dependent types (uN(32))). Put it in the environment.
Step 2: On a second pass, go through all inductive definitions, relations and function definitions:
  - for family types, special care is needed to remove the dependent typing so this will be done separately. (Skip for now)
  - For inductive types, make a fresh inductive type with the corresponding concrete type. Resolve any premises if possible. 
    Propagate this change to the location of the function call.
*)


open Il.Ast
open Il.Print

open Il.Eval
open Util.Source
open Util.Error


(* Env Creation and utility functions *)

module StringMap = Map.Make(String)
module IdSet = Set.Make(String)

type monoenv = 
{
  mutable calls: (Il.Ast.exp Queue.t) StringMap.t;
  mutable concrete_dependent_types: (Il.Ast.typ Queue.t) StringMap.t;
  mutable il_env: env;

}

let new_env() = 
{
    calls = StringMap.empty;
    concrete_dependent_types = StringMap.empty;
    il_env = Il.Env.empty;
}

let mono = "Monomorphization"

let print_env (m_env : monoenv) = 
  print_endline "Printing the Env: ";
  StringMap.iter (fun id exps -> Queue.iter (fun exp -> print_endline ("Call of id " ^ id ^ " : " ^ string_of_exp exp ^ " at: " ^ string_of_region exp.at)) exps ) m_env.calls;
  StringMap.iter (fun id typs -> Queue.iter (fun typ -> print_endline ("Concrete Dependent Type of id: " ^ id ^ " : " ^ string_of_typ typ ^ " at: " ^ string_of_region typ.at)) typs ) m_env.concrete_dependent_types

let bind m_env' id t =
  if id = "_" then m_env' else
    if StringMap.mem id m_env' 
      then StringMap.update id (Option.map (fun q -> Queue.push t q; q)) m_env'
      else StringMap.add id (let q = Queue.create () in Queue.push t q; q) m_env'

let concrete_dep_types_bind m_env id t =
  m_env.concrete_dependent_types <- bind m_env.concrete_dependent_types id t

let transform_atom (a : atom) = 
  match a.it with
    | Atom s -> s
    | _ -> ""

let is_atomid (a : atom) =
  match a.it with
    | Atom _ -> true
    | _ -> false

let to_string_mixop (m : mixop) = match m with
  | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> a
  | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )

let rec subst_and_reduce_prems (m_env : monoenv) (subst : subst) (prem : prem): prem = 
  match prem.it with
    | IfPr exp -> IfPr (Il.Eval.reduce_exp m_env.il_env (Il.Subst.subst_exp subst exp)) $ prem.at
    | IterPr (p, _) -> subst_and_reduce_prems m_env subst p
    | _ -> prem

(* Checking the existance of dependent types in a function argument list *)

(* let rec get_var_exp (exp : exp) : string list = 
  match exp.it with
    | VarE id -> [id.it]
    | TupE exps -> List.concat_map get_var_exp exps
    | CaseE (_, e) -> get_var_exp e
    | _ -> []

and get_var_typ (typ : typ) : string list =
  match typ.it with
    | VarT (_, args) -> List.concat_map get_var_arg args 
    | TupT exp_typ_pairs -> List.concat_map (fun (_, t) -> get_var_typ t) exp_typ_pairs
    | IterT (t, _) -> get_var_typ t
    | _ -> []

and get_var_arg (arg : arg) : string list =
  match arg.it with
    | ExpA exp -> get_var_exp exp
    | TypA typ -> get_var_typ typ
    | _ -> []

let rec check_dependent_types (arglist : arg list) (return_type : typ) : int list = 
  let rec f n arglist = 
    match arglist with
      | [] -> []
      | arg :: args -> let ids_used = get_var_typ return_type @ List.concat_map get_var_arg args |> IdSet.of_list in
        (if List.filter (fun a -> IdSet.mem a ids_used) (get_var_arg arg) <> [] 
          then [n]
          else []) @ f (n + 1) args in
  f 0 arglist  *)


(* Checking the existance of parametric types in a call argument list *)

let get_param_id_typ (typ : typ) : string  =
  match typ.it with
    | VarT (id, _) -> id.it
    | _ -> ""

let get_param_id_arg (arg : arg) : string =
  match arg.it with
    | TypA typ -> get_param_id_typ typ
    | _ -> ""

let check_parametric_types (arglist : arg list) : int list = 
  let rec f n arglist = 
    match arglist with
      | [] -> []
      | arg :: args -> 
        (if (get_param_id_arg arg) <> ""
          then [n]
          else []) @ f (n + 1) args in
  f 0 arglist 

(* String transformation Args *)

let rec to_string_exp (exp : exp) : string = 
  match exp.it with
    | BoolE _ | NumE _ | TextE _ -> string_of_exp exp
    | ListE exps -> "l" ^ String.concat "_" (List.map to_string_exp exps) 
    | TupE exps -> "t" ^ String.concat "_" (List.map to_string_exp exps) 
    | CaseE (mixop, exp) -> to_string_mixop mixop ^ "_" ^ to_string_exp exp
    | CvtE (e, _, _) -> to_string_exp e
    | SubE (e, _, _) -> to_string_exp e
    | _ -> error exp.at mono "Cannot transform these into strings"

and to_string_typ (typ : typ) : string = 
  match typ.it with
    | BoolT | NumT _ | TextT -> string_of_typ typ
    | VarT (id, args) -> id.it ^ "_" ^ String.concat "__" (List.map to_string_arg args)
    | IterT (typ, iter) -> string_of_typ typ ^ "_" ^ string_of_iter iter
    | TupT exp_typ_pairs -> "tt" ^ String.concat "_" (List.map (fun (e, t) -> to_string_exp e ^ to_string_typ t) exp_typ_pairs) 

and to_string_arg (arg : arg): string =
  match arg.it with
    | ExpA exp -> to_string_exp exp
    | TypA typ -> to_string_typ typ
    | _ -> ""

and transform_id (id : id) (args : arg list): id =
  id.it ^ "_mono_" ^ String.concat "__" (List.map to_string_arg args) $ id.at

(* Terminal cases traversal *)

let rec check_reducible_exp (exp : exp) : bool =
  match exp.it with
    | BoolE _ | NumE _ | TextE _ -> true
    | UnE (_, _, e) -> check_reducible_exp e
    | BinE (_, _, e1, e2) -> check_reducible_exp e1 && check_reducible_exp e2
    | CmpE (_, _, e1, e2) -> check_reducible_exp e1 && check_reducible_exp e2
    | TupE exps -> List.fold_left (fun acc e -> acc && check_reducible_exp e) true exps 
    | CvtE (e, _, _) -> check_reducible_exp e
    | SubE (e, _, _) -> check_reducible_exp e
    | ListE exps -> List.fold_left (fun acc e -> acc && check_reducible_exp e) true exps 
    | CaseE (_, e) -> check_reducible_exp e
    | _ -> false

and check_reducible_typ (typ: typ): bool =
  match typ.it with
    | IterT (t, _iter) -> check_reducible_typ t
    | VarT (_, args) -> check_reducible_args args
    | TupT exp_typ_pairs -> List.fold_left (fun acc (_e, t) -> acc && check_reducible_typ t) true exp_typ_pairs
    | _ -> true

and check_reducible_arg (arg: arg): bool =
  match arg.it with
    | TypA typ -> check_reducible_typ typ
    | ExpA exp -> check_reducible_exp exp
    | _ -> false

and check_reducible_args (args: arg list): bool =
  List.fold_left (fun acc arg -> acc && check_reducible_arg arg) true args


(* Populating the Environment Traversal *)

let rec populate_env_typ (m_env : monoenv) (typ : typ) = 
  match typ.it with
    | VarT (id, args) when args <> [] && check_reducible_args args ->
      m_env.concrete_dependent_types <- bind m_env.concrete_dependent_types id.it typ
    | VarT (_id, args) -> List.iter (populate_env_arg m_env) args
    | IterT (t, _) -> populate_env_typ m_env t
    | TupT exp_typ_pairs -> List.iter (fun (_, t) -> populate_env_typ m_env t) exp_typ_pairs
    | _ -> ()

and populate_env_exp (m_env : monoenv) (exp : exp) =
  match exp.it with
    | CallE (id, args) when check_parametric_types args <> [] -> m_env.calls <- bind m_env.calls id.it exp; List.iter (populate_env_arg m_env) args
    | CallE (_id, args) -> List.iter (populate_env_arg m_env) args
    | UnE (_, _, e) -> populate_env_exp m_env e
    | BinE (_, _, e1, e2) -> populate_env_exp m_env e1; populate_env_exp m_env e2
    | CmpE (_, _, e1, e2) -> populate_env_exp m_env e1; populate_env_exp m_env e2
    | TupE exps -> List.iter (populate_env_exp m_env) exps
    | ProjE (e, _) -> populate_env_exp m_env e
    | CaseE (_, e) -> populate_env_exp m_env e
    | UncaseE (e, _) -> populate_env_exp m_env e
    | OptE (Some e) -> populate_env_exp m_env e
    | TheE e -> populate_env_exp m_env e
    | StrE expfields -> List.iter (fun (_, e) -> populate_env_exp m_env e) expfields
    | DotE (e, _) -> populate_env_exp m_env e
    | CompE (e1, e2) -> populate_env_exp m_env e1; populate_env_exp m_env e2
    | ListE exps -> List.iter (populate_env_exp m_env) exps
    | LiftE e -> populate_env_exp m_env e
    | MemE (e1, e2) -> populate_env_exp m_env e1; populate_env_exp m_env e2
    | LenE e -> populate_env_exp m_env e
    | CatE (e1, e2) -> populate_env_exp m_env e1; populate_env_exp m_env e2
    | IdxE (e1, e2) -> populate_env_exp m_env e1; populate_env_exp m_env e2
    | SliceE (e1, e2, e3) -> populate_env_exp m_env e1; populate_env_exp m_env e2; populate_env_exp m_env e3
    | UpdE (e1, path, e2) -> populate_env_exp m_env e1; populate_env_path m_env path; populate_env_exp m_env e2
    | ExtE (e1, path, e2) -> populate_env_exp m_env e1; populate_env_path m_env path; populate_env_exp m_env e2
    | IterE (e, (_, id_exp_pairs)) -> populate_env_exp m_env e; List.iter (fun (_, e) -> populate_env_exp m_env e) id_exp_pairs
    | CvtE (e, _, _) -> populate_env_exp m_env e
    | SubE (e, t1, t2) -> populate_env_exp m_env e; populate_env_typ m_env t1; populate_env_typ m_env t2
    | _ -> ()
  
and populate_env_path (m_env : monoenv) (path : path) = 
  match path.it with
    | IdxP (p, e) -> populate_env_path m_env p; populate_env_exp m_env e
    | SliceP (p, e1, e2) -> populate_env_path m_env p; populate_env_exp m_env e1; populate_env_exp m_env e2
    | DotP (p, _) -> populate_env_path m_env p
    | RootP -> ()

and populate_env_arg (m_env : monoenv) (arg: arg) = 
  match arg.it with
    | ExpA exp -> populate_env_exp m_env exp
    | TypA typ -> populate_env_typ m_env typ
    | _ -> ()

let populate_env_bind (m_env : monoenv) (bind : bind) =
  match bind.it with 
    | ExpB (_, typ) -> populate_env_typ m_env typ
    | _ -> ()
  
let rec populate_env_prem (m_env : monoenv) (prem: prem) =
  match prem.it with
    | RulePr (_, _, exp) -> populate_env_exp m_env exp
    | IfPr exp -> populate_env_exp m_env exp
    | LetPr (e1, e2, _) -> populate_env_exp m_env e1; populate_env_exp m_env e2
    | ElsePr -> ()
    | IterPr (prem, (_, id_exp_pairs)) -> populate_env_prem m_env prem; List.iter (fun (_, e) -> populate_env_exp m_env e) id_exp_pairs

let populate_env_param (m_env : monoenv) (param : param) = 
  match param.it with
    | ExpP (_, typ) -> populate_env_typ m_env typ
    | _ -> ()

let populate_env_instance (m_env : monoenv) (inst: inst) =
  match inst.it with
    | InstD (binds, args, deftyp) -> List.iter (populate_env_bind m_env) binds; List.iter (populate_env_arg m_env) args;
    (match deftyp.it with
      | AliasT typ -> populate_env_typ m_env typ
      | StructT typfields -> List.iter (fun (_, (_, typ, _), _) -> populate_env_typ m_env typ) typfields
      | VariantT typcases -> List.iter (fun (_, (_, typ, _), _) -> populate_env_typ m_env typ) typcases
    )

let populate_env_rule (m_env : monoenv) (rule : rule) = 
  match rule.it with
    | RuleD (_, binds, _, e, prems) -> List.iter (populate_env_bind m_env) binds; populate_env_exp m_env e; List.iter (populate_env_prem m_env) prems 

let populate_env_clause (m_env : monoenv) (clause : clause) =
  match clause.it with
    | DefD (binds, args, exp, prems) -> List.iter (populate_env_bind m_env) binds; List.iter (populate_env_arg m_env) args; populate_env_exp m_env exp;
      List.iter (populate_env_prem m_env) prems

let rec populate_env_def (m_env : monoenv) (def : def) = 
  match def.it with
    | TypD (_id, params, instances) -> List.iter (populate_env_param m_env) params; List.iter (populate_env_instance m_env) instances
    | RelD (_id, _mixop, typ, rules) -> populate_env_typ m_env typ; 
      List.iter (populate_env_rule m_env) rules
    | DecD (_, params, typ, clauses) -> List.iter (populate_env_param m_env) params; populate_env_typ m_env typ; List.iter (populate_env_clause m_env) clauses 
    | RecD defs -> List.iter (populate_env_def m_env) defs
    | _ -> ()

(* Monomorphization Pass *)

let create_args_pairings (args_ids : id list) (concrete_args : arg list): subst =
  List.fold_left (fun acc (id, arg) -> match arg.it with
    | ExpA exp -> Il.Subst.add_varid acc id exp
    | TypA typ -> Il.Subst.add_typid acc id typ
    | DefA x -> Il.Subst.add_defid acc id x
    | GramA g -> Il.Subst.add_gramid acc id g) Il.Subst.empty (List.combine args_ids concrete_args)

let replace_args (subst : subst) (args: arg list): arg list =
  Il.Subst.subst_args subst args

let evaluate_args (m_env : monoenv) (args : arg list): arg list =
  List.map (fun arg -> reduce_arg m_env.il_env arg) args

let get_dependent_type_args (typ : typ) = 
  match typ.it with  
    | VarT (_, concrete_args) -> concrete_args
    | _ -> error typ.at mono "Applied monomorphization on a non-concrete dependent type"

let get_variables_from_arg (arg : arg): id = 
  match arg.it with
    | ExpA ({it = VarE id; _}) -> id
    | TypA ({it = VarT (id, _); _}) -> id
    | _ -> error arg.at mono "Arguments on LHS have something other than id"
  
let rec transform_dependent_type (m_env : monoenv) (typ : typ) (subst: subst): typ = 
  let subst_empty = (subst = Il.Subst.empty) in 
  (match typ.it with
    | VarT (id, args) when args <> [] -> 
      let args_replaced = replace_args subst args in
      if check_reducible_args args_replaced 
        then 
          let args_evaluated = evaluate_args m_env args_replaced in
          (if not subst_empty then concrete_dep_types_bind m_env id.it (VarT(id, args_evaluated) $ typ.at)); 
          VarT (transform_id id args_evaluated, []) 
        else error typ.at mono "Cannot monomorphize correctly"
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (e, transform_dependent_type m_env t subst)) exp_typ_pairs)
    | IterT (t, iter) -> IterT (transform_dependent_type m_env t subst, iter)
    | t -> t
  ) $ typ.at

let transform_type_creation (m_env : monoenv) (id : id) (inst : inst) (at : Util.Source.region) : def list =
  match inst.it with 
    | InstD (binds, args, deftyp) -> (match deftyp.it with 
      | AliasT typ -> (match StringMap.find_opt id.it m_env.concrete_dependent_types with
        | None -> let new_deftyp = AliasT (transform_dependent_type m_env typ Il.Subst.empty) $ deftyp.at in 
          [(TypD (id, [], [InstD (binds, [], new_deftyp) $ inst.at]) $ at)]
        | Some q -> 
          let rec loop () = 
            (match Queue.take_opt q with
              | None -> []
              | Some t -> let dep_args = evaluate_args m_env (get_dependent_type_args t) in 
                let args_ids = List.map get_variables_from_arg args in  
                let subst = create_args_pairings args_ids dep_args in
                let new_deftyp = AliasT (transform_dependent_type m_env typ subst) $ deftyp.at in 
                (TypD (transform_id id dep_args, [], [InstD ([], [], new_deftyp) $ inst.at]) $ at) :: loop ()
            ) in 
          loop () 
      )
      | StructT typfields -> (
        let new_deftyp = StructT (List.map (fun (a, (bs, t, prems), hints) -> (a, (bs, transform_dependent_type m_env t Il.Subst.empty, prems), hints)) typfields) $ deftyp.at in
        [TypD (id, [], [InstD ([], [], new_deftyp) $ inst.at]) $ at] (* Ignore args for now, there shouldn't be any here *)
      )
      | VariantT typcases -> (match StringMap.find_opt id.it m_env.concrete_dependent_types with
        | None -> let new_deftyp = VariantT (List.map (fun (m, (bs, t, prems), hints) -> (m, (bs, transform_dependent_type m_env t Il.Subst.empty, prems), hints)) typcases) $ deftyp.at in
          [TypD (id, [], [InstD ([], [], new_deftyp) $ inst.at]) $ at] 
        | Some q ->
          let rec loop () = 
            (match Queue.take_opt q with
              | None -> []
              | Some t -> let dep_args = evaluate_args m_env (get_dependent_type_args t) in 
                let args_ids = List.map get_variables_from_arg args in  
                let subst = create_args_pairings args_ids dep_args in
                let new_deftyp = VariantT (List.map (fun (m, (bs, t, prems), hints) -> (m, (bs, transform_dependent_type m_env t subst, List.map (subst_and_reduce_prems m_env subst) prems), hints)) typcases) $ deftyp.at in 
                (TypD (transform_id id dep_args, [], [InstD ([], [], new_deftyp) $ inst.at]) $ at) :: loop ()
            ) in 
          loop ()
      )
    )

let rec transform_def (m_env : monoenv) (def : def) : def list =
  match def.it with
    | TypD (id, _, [inst]) -> transform_type_creation m_env id inst def.at
    | TypD (_id, _params, _insts) -> [def] (* TODO: Ignore family types for now *)
    | RelD (_id, _mixop, _typ, _rules) -> [def]
    | DecD (_id, _params, _typ, _clauses) -> [def]
    | RecD defs -> List.concat_map (transform_def m_env) defs 
    | _ -> [def]    

(* Main transformation function *)
let transform (script: Il.Ast.script) =
  let m_env = new_env() in 
  List.iter (populate_env_def m_env) script;
  m_env.il_env <- Il.Env.env_of_script script;
  print_env m_env;

  (* Reverse the script in order to monomorphize nested ones correctly *)
  let transformed_script = List.rev (List.concat_map (transform_def m_env) (List.rev script)) in
  print_env m_env;
  transformed_script

