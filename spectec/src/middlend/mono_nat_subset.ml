open Il.Ast
open Il

open Util.Source
open Util.Error
open Xl.Num
open Xl.Atom

let map_snd f = List.map (fun (v1, v2) -> (v1, f v2))

let map_func_suffix = "_to_nat"
let map_fun_prefix = "nat_to_"
let pass_string = "Monomorphization"

let pass_error at msg = error at pass_string msg

let case_prefix = "MONO__"

module StringMap = Map.Make(String)

type pass_env = {
  mutable nat_subs_set: (nat list) StringMap.t
}

let empty_pass_env = {
  nat_subs_set = StringMap.empty
}

let empty_tuple = TupE [] $$ no_region % (TupT [] $ no_region)

let create_option_exp exp typ = 
  OptE(exp) $$ no_region % (IterT (typ, Opt) $ no_region)

let add_to_nat_set (env : pass_env) (id : id) (nat_list: nat list): unit =
  env.nat_subs_set <- StringMap.add id.it nat_list env.nat_subs_set

let rec check_nat_type (typ: Il.Ast.typ): bool = 
  match typ.it with
    | NumT `NatT -> true
    | TupT exp_typ_pairs -> (match exp_typ_pairs with
      | [(_e, t)] -> check_nat_type t
      | _ -> false
    )
    | _ -> false

let is_disjuntion_exp (exp : exp): bool =
  match exp.it with 
    | BinE (`OrOp, `BoolT, _e1, _e2) -> true
    | _ -> false

let is_nat_eq_exp (exp : exp): bool =
  match exp.it with 
    | CmpE (`EqOp, _, _e1, _e2) -> true
    | _ -> false

let is_nat_exp (exp : exp): bool = 
  match exp.it with
    | NumE _ -> true
    | _ -> false

let is_var_exp (exp : exp): bool =
  match exp.it with
    | VarE _ -> check_nat_type exp.note
    | _ -> false

let rec check_subset_nat (exp : exp): bool =
  match exp.it with
    | BinE (`OrOp, `BoolT, e1, e2) ->
      (is_disjuntion_exp e1 || is_nat_eq_exp e1) && is_nat_eq_exp e2 &&
      check_subset_nat e1 && check_subset_nat e2
    | CmpE (`EqOp, _, e1, e2) -> is_var_exp e1 && is_nat_exp e2
    | _ -> false

let rec get_nat_list (exp : exp): nat list = 
  match exp.it with
    | NumE (`Nat n) -> [n]
    | CmpE (`EqOp, _, e1, e2) | BinE (`OrOp, `BoolT, e1, e2) -> get_nat_list e1 @ get_nat_list e2
    | _ -> []

let get_inst_params (inst : inst): bind list * arg list * deftyp = 
  match inst.it with
    | InstD (binds, args, deftyp) -> (binds, args, deftyp)

(* TODO fill necessary info *)
let create_mixop (at : Util.Source.region) (id : string): mixop =
  [[Atom id $$ at % (info "")]]

let create_mapping_functions (id : id) (at : Util.Source.region) (nat_list : nat list) =
  let fresh_id = "x" $ at in
  let new_id = (id.it ^ map_func_suffix) $ id.at in
  let new_id_inv = (map_fun_prefix ^ id.it) $ id.at in
  let new_typ = (NumT `NatT) $ at in
  let user_typ = VarT (id, []) $ at in 
  let opt_typ = IterT(user_typ, Opt) $ at in
  let new_param = ExpP (fresh_id, user_typ) $ at in
  let new_param_inv = ExpP(fresh_id, new_typ) $ at in 
  let empty_tuple = TupE [] $$ at % (TupT [] $ at) in
  let num_exp n = NumE (`Nat n) $$ at % new_typ in 
  let new_clauses = List.map (fun n -> 
    let mixop = create_mixop at (case_prefix ^ Z.to_string n) in
    let exp = CaseE (mixop, empty_tuple) $$ at % user_typ in
    DefD ([], [ExpA exp $ at], num_exp n, []) $ at
  ) nat_list in
  let new_clauses_inv = List.map (fun n -> 
    let mixop = create_mixop at (case_prefix ^ Z.to_string n) in
    let exp = CaseE (mixop, empty_tuple) $$ at % user_typ in
    DefD ([], [ExpA (num_exp n) $ at], create_option_exp (Some exp) user_typ, []) $ at
  ) nat_list in
  let empty_clause = DefD([ExpB(fresh_id, new_typ) $ at], [ExpA (VarE fresh_id $$ at % new_typ) $ at], create_option_exp None user_typ, []) $ at in
  [DecD(new_id, [new_param], new_typ, new_clauses); DecD(new_id_inv, [new_param_inv], opt_typ, new_clauses_inv @ [empty_clause])]

let rec transform_type (env : pass_env) (typ : Il.Ast.typ): Il.Ast.typ =
  (match typ.it with
    | VarT (id, args) -> VarT (id, List.map (transform_arg env) args)
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (transform_exp env e, transform_type env t)) exp_typ_pairs)
    | IterT (t, iter) -> IterT (transform_type env t, iter)
    | _ -> typ.it
  ) $ typ.at

and transform_exp (env : pass_env) (exp : exp): exp =
  let t_func = transform_exp env in
  (match exp.it with
    | UnE (unop, optyp, e) -> UnE (unop, optyp, t_func e)
    | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2)
    | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2)
    | TupE exps -> TupE (List.map t_func exps)
    | ProjE ({it = UncaseE (e, _); _} as e1, i) -> 
      let id = Print.string_of_typ_name e.note in 
      if (StringMap.mem id env.nat_subs_set) 
        then CallE (Print.string_of_typ_name e.note ^ map_func_suffix $ e.at, [ExpA e $ e.at]) 
        else ProjE (t_func e1, i)
    | ProjE (e, i) -> ProjE (t_func e, i)
    | CaseE (m, ({it = TupE []; _} as e)) -> CaseE (m, e) 
    | CaseE (m, ({it = TupE exps; _} as e))  -> 
      let id = (Print.string_of_typ_name exp.note) in 
      (match (StringMap.find_opt id env.nat_subs_set) with
        | None -> CaseE (m, t_func e)
        | Some nat_list -> transform_case exp.note env exps exp nat_list
      )
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
    | UpdE (e1, path, e2) -> UpdE (t_func e1, transform_path env path, t_func e2)
    | ExtE (e1, path, e2) -> ExtE (t_func e1, transform_path env path, t_func e2)
    | CallE (id, args) -> CallE (id, List.map (transform_arg env) args)
    | IterE (e, iterexp) -> IterE (t_func e, transform_iterexp env iterexp)
    | CvtE (e, ntyp1, ntyp2) -> CvtE (t_func e, ntyp1, ntyp2)
    | SubE (e, t1, t2) -> SubE (t_func e, transform_type env t1, transform_type env t2)
    | e -> e
  ) $$ exp.at % (transform_type env exp.note)

and transform_iterexp (env : pass_env) (iterexp : iterexp): iterexp = 
  let (iter, id_exp_pairs) = iterexp in
  (iter, map_snd (transform_exp env) id_exp_pairs)

and transform_case (typ : Il.Ast.typ) (env : pass_env) (exps : exp list) (default : exp) (nat_list : nat list): exp' =
  let id = (Print.string_of_typ_name typ) in 
  match exps with
    | [{it = NumE (`Nat n); _}] -> 
      if List.mem n nat_list
        then CaseE (create_mixop no_region (case_prefix ^ (Z.to_string n)), empty_tuple) 
        else pass_error default.at ("Cannot monomorphize case that does not exist for nat: " ^ Z.to_string n)
    | [e] -> TheE (CallE (map_fun_prefix ^ id $ e.at, [ExpA (transform_exp env e) $ e.at]) $$ e.at % (IterT(typ, Opt) $ no_region))
    | _ -> pass_error default.at "Must have only one expression in case" (* Should not happen due to validation *)
    
and transform_path (env : pass_env) (path : path): path = 
  (match path.it with
    | RootP -> RootP
    | IdxP (p, e) -> IdxP (transform_path env p, transform_exp env e)
    | SliceP (p, e1, e2) -> SliceP (transform_path env p, transform_exp env e1, transform_exp env e2)
    | DotP (p, a) -> DotP (transform_path env p, a)
  ) $$ path.at % transform_type env path.note

and transform_arg (env : pass_env) (arg : arg): arg =
  (match arg.it with
    | ExpA exp -> ExpA (transform_exp env exp)
    | TypA typ -> TypA (transform_type env typ)
    | _ -> arg.it
  ) $ arg.at

and transform_bind (env : pass_env) (bind : bind): bind =
  (match bind.it with
    | ExpB (id, typ) -> ExpB (id, transform_type env typ)
    | b -> b
  ) $ bind.at

and transform_param (env : pass_env) (param : param): param =
  (match param.it with
    | ExpP (id, typ) -> ExpP (id, transform_type env typ)
    | p -> p
  ) $ param.at

and transform_prem (env : pass_env) (prem : prem): prem =
  (match prem.it with
    | IfPr e -> IfPr (transform_exp env e)
    | RulePr (id, m, e) -> RulePr (id, m, transform_exp env e)
    | LetPr (e1, e2, ids) -> LetPr (transform_exp env e1, transform_exp env e2, ids)
    | ElsePr -> ElsePr
    | IterPr (prem, iterexp) -> IterPr (transform_prem env prem, transform_iterexp env iterexp)
  ) $ prem.at

let transform_type_creation (env : pass_env) (id : id) (inst : inst): inst * def' list =
  let (binds, args, deftyp) = get_inst_params inst in 
  let reconstruct_typ dtyp new_defs = (InstD (binds, List.map (transform_arg env) args, dtyp $ deftyp.at) $ inst.at, new_defs) in
  match deftyp.it with
    | VariantT [(_, (_, t, [{it = IfPr exp; _}]), _)] when check_nat_type t && check_subset_nat exp -> 
      let nat_list = get_nat_list exp in 
      if nat_list = [] then (inst, []) else
      let new_cases = List.map (fun n ->
        (create_mixop inst.at (case_prefix ^ Z.to_string n), ([], TupT [] $ inst.at, []), [])
      ) nat_list in
      add_to_nat_set env id nat_list;
      reconstruct_typ (VariantT new_cases) (create_mapping_functions id inst.at nat_list)
    | VariantT typcases -> reconstruct_typ (VariantT (List.map (fun (m, (case_binds, t, prems), hints) ->
        (m, (List.map (transform_bind env) case_binds, transform_type env t, List.map (transform_prem env) prems), hints)
      ) typcases)) []
    | StructT typfields -> reconstruct_typ (StructT (List.map (fun (a, (case_binds, t, prems), hints) ->
        (a, (List.map (transform_bind env) case_binds, transform_type env t, List.map (transform_prem env) prems), hints)
      ) typfields)) []
    | AliasT typ -> reconstruct_typ (AliasT (transform_type env typ)) []

let transform_rule (env : pass_env) (rule : rule): rule =
  (match rule.it with
    | RuleD (id, binds, m, exp, prems) -> 
      RuleD (id, List.map (transform_bind env) binds, m, transform_exp env exp, List.map (transform_prem env) prems)
  ) $ rule.at

let transform_clause (env : pass_env) (clause : clause): clause =
  (match clause.it with
    | DefD (binds, args, exp, prems) -> 
      DefD (List.map (transform_bind env) binds, 
        List.map (transform_arg env) args, 
        transform_exp env exp, List.map (transform_prem env) prems)
  ) $ clause.at

let transform_inst (env : pass_env) (inst : inst): inst =
  (match inst.it with
    | InstD (binds, args, deftyp) -> InstD (List.map (transform_bind env) binds, List.map (transform_arg env) args, (match deftyp.it with
      | VariantT typcases -> VariantT (List.map (fun (m, (t_binds, typ, prems), hints) -> (m, (List.map (transform_bind env) t_binds, transform_type env typ, List.map (transform_prem env) prems), hints)) typcases) 
      | StructT typfields -> StructT (List.map (fun (a, (t_binds, typ, prems), hints) -> (a, (List.map (transform_bind env) t_binds, transform_type env typ, List.map (transform_prem env) prems), hints)) typfields) 
      | AliasT typ -> AliasT (transform_type env typ)
    ) $ deftyp.at)
  ) $ inst.at

let rec transform_def (env : pass_env) (def : def): def list = 
  (match def.it with
    | TypD (id, params, [inst]) -> let (new_inst, new_defs) = transform_type_creation env id inst in
      [TypD (id, List.map (transform_param env) params, [new_inst])] @ new_defs
    | TypD (id, params, insts) -> [TypD(id, List.map (transform_param env) params, List.map (transform_inst env) insts)] (* TODO think of extending this? *)
    | RelD (id, mixop, typ, rules) -> [RelD (id, mixop, transform_type env typ, List.map (transform_rule env) rules)]
    | DecD (id, params, typ, clauses) -> [DecD (id, List.map (transform_param env) params, transform_type env typ, List.map (transform_clause env) clauses)]
    | RecD defs -> [RecD (List.concat_map (transform_def env) defs)]
    | _ -> [def.it]
  ) |> List.map (fun d' -> d' $ def.at)

let transform (script : script) =
  let pass = empty_pass_env in 
  List.concat_map (transform_def pass) script, pass
