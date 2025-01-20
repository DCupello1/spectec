


(* 
Step 1: Grab all concrete calls (i.e. in function calls $func(32) or dependent types (uN(32))). Put it in the environment.
Step 2: On a second pass, go through all inductive definitions, relations and function definitions:
  - for family types, special care is needed to remove the dependent typing so this will be done separately. (Skip for now)
  - For inductive types, make a fresh inductive type with the corresponding concrete type. Resolve any premises if possible. 
    Propagate this change to the location of the function call.
*)


open Il.Ast
open Il.Print
open Util.Source
open Util.Error


(* Env Creation and utility functions *)

module Env = Map.Make(String)

type env = 
{
  mutable calls: (Il.Ast.exp list) Env.t;
  mutable concrete_dependent_types: (Il.Ast.typ list) Env.t;
}

let new_env() = 
{
    calls = Env.empty;
    concrete_dependent_types = Env.empty
}

let mono = "Monomorphization"

let print_env (env : env) = 
  print_endline "Printing the Env: ";
  Env.iter (fun _ exps -> List.iter (fun exp -> print_endline ("Call: " ^ string_of_exp exp ^ " at: " ^ string_of_region exp.at)) exps ) env.calls;
  Env.iter (fun _ typs -> List.iter (fun typ -> print_endline ("Concrete Dependent Type: " ^ string_of_typ typ ^ " at: " ^ string_of_region typ.at)) typs ) env.concrete_dependent_types

let bind env' id t =
  if id = "_" then env' else
    if Env.mem id env' 
      then Env.update id (Option.map (fun lst -> t :: lst)) env'
      else Env.add id [t] env'

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

(* Terminal cases traversal *)

let rec check_terminal_exp (exp : exp) : bool =
  match exp.it with
    | BoolE _ -> true
    | NumE _ -> true
    | TextE _ -> true
    | UnE (_, _, e) -> check_terminal_exp e
    | BinE (_, _, e1, e2) -> check_terminal_exp e1 && check_terminal_exp e2
    | CmpE (_, _, e1, e2) -> check_terminal_exp e1 && check_terminal_exp e2
    | TupE exps -> List.fold_left (fun acc e -> acc && check_terminal_exp e) true exps 
    | CvtE (e, _, _) -> check_terminal_exp e
    | SubE (e, _, _) -> check_terminal_exp e
    | ListE exps -> List.fold_left (fun acc e -> acc && check_terminal_exp e) true exps 
    | CaseE (_, e) -> check_terminal_exp e
    | _ -> false

and check_terminal_typ (typ: typ): bool =
  match typ.it with
    | BoolT -> true
    | NumT _ -> true
    | TextT -> true
    | IterT (t, _iter) -> check_terminal_typ t
    | _ -> false

and check_terminal_arg (arg: arg): bool =
  match arg.it with
    | TypA typ -> check_terminal_typ typ
    | ExpA exp -> check_terminal_exp exp
    | _ -> false

let check_terminal_args (args: arg list): bool =
  List.fold_left (fun acc arg -> acc && check_terminal_arg arg) true args


(* Populating the Environment Traversal *)

let rec populate_env_typ (env : env) (typ : typ) = 
  match typ.it with
    | VarT (id, args) when List.length args <> 0 && check_terminal_args args ->
      env.concrete_dependent_types <- bind env.concrete_dependent_types id.it typ
    | VarT (_id, args) -> List.iter (populate_env_arg env) args
    | IterT (t, _) -> populate_env_typ env t
    | TupT exp_typ_pairs -> List.iter (fun (_, t) -> populate_env_typ env t) exp_typ_pairs
    | _ -> ()

and populate_env_exp (env : env) (exp : exp) =
  match exp.it with
    | CallE (id, args) -> env.calls <- bind env.calls id.it exp; List.iter (populate_env_arg env) args
    | UnE (_, _, e) -> populate_env_exp env e
    | BinE (_, _, e1, e2) -> populate_env_exp env e1; populate_env_exp env e2
    | CmpE (_, _, e1, e2) -> populate_env_exp env e1; populate_env_exp env e2
    | TupE exps -> List.iter (populate_env_exp env) exps
    | ProjE (e, _) -> populate_env_exp env e
    | CaseE (_, e) -> populate_env_exp env e
    | UncaseE (e, _) -> populate_env_exp env e
    | OptE (Some e) -> populate_env_exp env e
    | TheE e -> populate_env_exp env e
    | StrE expfields -> List.iter (fun (_, e) -> populate_env_exp env e) expfields
    | DotE (e, _) -> populate_env_exp env e
    | CompE (e1, e2) -> populate_env_exp env e1; populate_env_exp env e2
    | ListE exps -> List.iter (populate_env_exp env) exps
    | LiftE e -> populate_env_exp env e
    | MemE (e1, e2) -> populate_env_exp env e1; populate_env_exp env e2
    | LenE e -> populate_env_exp env e
    | CatE (e1, e2) -> populate_env_exp env e1; populate_env_exp env e2
    | IdxE (e1, e2) -> populate_env_exp env e1; populate_env_exp env e2
    | SliceE (e1, e2, e3) -> populate_env_exp env e1; populate_env_exp env e2; populate_env_exp env e3
    | UpdE (e1, path, e2) -> populate_env_exp env e1; populate_env_path env path; populate_env_exp env e2
    | ExtE (e1, path, e2) -> populate_env_exp env e1; populate_env_path env path; populate_env_exp env e2
    | IterE (e, (_, id_exp_pairs)) -> populate_env_exp env e; List.iter (fun (_, e) -> populate_env_exp env e) id_exp_pairs
    | CvtE (e, _, _) -> populate_env_exp env e
    | SubE (e, t1, t2) -> populate_env_exp env e; populate_env_typ env t1; populate_env_typ env t2
    | _ -> ()
  
and populate_env_path (env : env) (path : path) = 
  match path.it with
    | IdxP (p, e) -> populate_env_path env p; populate_env_exp env e
    | SliceP (p, e1, e2) -> populate_env_path env p; populate_env_exp env e1; populate_env_exp env e2
    | DotP (p, _) -> populate_env_path env p
    | RootP -> ()

and populate_env_arg (env : env) (arg: arg) = 
  match arg.it with
    | ExpA exp -> populate_env_exp env exp
    | TypA typ -> populate_env_typ env typ
    | _ -> ()

let populate_env_bind (env : env) (bind : bind) =
  match bind.it with 
    | ExpB (_, typ) -> populate_env_typ env typ
    | _ -> ()
  
let rec populate_env_prem (env : env) (prem: prem) =
  match prem.it with
    | RulePr (_, _, exp) -> populate_env_exp env exp
    | IfPr exp -> populate_env_exp env exp
    | LetPr (e1, e2, _) -> populate_env_exp env e1; populate_env_exp env e2
    | ElsePr -> ()
    | IterPr (prem, (_, id_exp_pairs)) -> populate_env_prem env prem; List.iter (fun (_, e) -> populate_env_exp env e) id_exp_pairs

let populate_env_param (env : env) (param : param) = 
  match param.it with
    | ExpP (_, typ) -> populate_env_typ env typ
    | _ -> ()

let populate_env_instance (env : env) (inst: inst) =
  match inst.it with
    | InstD (binds, args, deftyp) -> List.iter (populate_env_bind env) binds; List.iter (populate_env_arg env) args;
    (match deftyp.it with
      | AliasT typ -> populate_env_typ env typ
      | StructT typfields -> List.iter (fun (_, (_, typ, _), _) -> populate_env_typ env typ) typfields
      | VariantT typcases -> List.iter (fun (_, (_, typ, _), _) -> populate_env_typ env typ) typcases
    )

let populate_env_rule (env : env) (rule : rule) = 
  match rule.it with
    | RuleD (_, binds, _, e, prems) -> List.iter (populate_env_bind env) binds; populate_env_exp env e; List.iter (populate_env_prem env) prems 

let populate_env_clause (env : env) (clause : clause) =
  match clause.it with
    | DefD (binds, args, exp, prems) -> List.iter (populate_env_bind env) binds; List.iter (populate_env_arg env) args; populate_env_exp env exp;
      List.iter (populate_env_prem env) prems

let rec populate_env_def (env : env) (def : def) = 
  match def.it with
    | TypD (_id, params, instances) -> List.iter (populate_env_param env) params; List.iter (populate_env_instance env) instances
    | RelD (_id, _mixop, typ, rules) -> populate_env_typ env typ; 
      List.iter (populate_env_rule env) rules
    | DecD (_, params, typ, clauses) -> List.iter (populate_env_param env) params; populate_env_typ env typ; List.iter (populate_env_clause env) clauses 
    | RecD defs -> List.iter (populate_env_def env) defs
    | _ -> ()

(* Monomorphization Pass *)

let transform_type_creation (env : env) (inst : inst) =
  match inst.it with 
    | InstD (binds, args, deftyp) -> (match deftyp.it with 
      | AliasT typ -> []
      | StructT typfields -> []
      | VariantT typcases -> [] 
    )

let rec transform_def (env : env) (def : def) : def list =
  match def.it with
    | TypD (id, params, [inst]) -> []
    | RelD (id, mixop, typ, rules) -> []
    | DecD (id, params, typ, clauses) -> []
    | RecD defs -> List.concat_map (transform_def env) defs 
    | _ -> [def]    

(* Main transformation function *)
let transform (script: Il.Ast.script) =
  let env = new_env() in 
  List.iter (populate_env_def env) script;
  script
