open Il.Ast
open Il

open Util.Source
open Util.Error
open Xl.Num
open Xl.Atom

let map_snd f = List.map (fun (v1, v2) -> (v1, f v2))

let map_func_suffix = "_to_nat"
let pass_string = "Monomorphization"

let pass_error at msg = error at pass_string msg

let bind_suffix = "_m_" 
let case_prefix = "MONO__"

module ExpMap = Map.Make(struct
  type t = Ast.exp
  let compare exp1 exp2 = 
    if Eq.eq_exp exp1 exp2 then 0
    else String.compare (Print.string_of_exp exp1) (Print.string_of_exp exp2) (* HACK - Need better way to compare expressions, only hurts performance *)
end
)

let _print_exp_map exp_map = 
  print_endline "Printing Exp Map:";
  ExpMap.iter (fun exp (id, typ_id) -> 
    print_endline (Print.string_of_exp exp ^ " {" ^ id.it ^ " : " ^ typ_id.it ^ "}")
    ) exp_map

module StringMap = Map.Make(String)

type pass_env = {
  mutable nat_subs_set: (nat list) StringMap.t
  (* mutable vars_used:  *)
}

let empty_pass_env = {
  nat_subs_set = StringMap.empty
}

let empty_tuple = TupE [] $$ no_region % (TupT [] $ no_region)

let create_cmp exp1 exp2 = CmpE (`EqOp, `BoolT, exp1, exp2) $$ no_region % (NumT (`NatT) $ no_region)  

let create_var_exp id typ_id = VarE id $$ no_region % (VarT (typ_id, []) $ no_region) 

let create_nat_call_exp id args = CallE(id, args) $$ no_region % (NumT `NatT $ no_region)

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

let exp_iter_for_cases (env : pass_env): (id * id) ExpMap.t ref * (module Iter.Arg) = 
  let module Arg =
    struct
      include Iter.Skip
      let acc = ref ExpMap.empty
      let acc_i = ref 1

      let visit_exp e =
        match e.it with 
          | CaseE (_m, {it = TupE exps; _}) ->
            let typ_name = Print.string_of_typ_name e.note in
            if (StringMap.mem typ_name env.nat_subs_set) && (List.length exps = 1) 
              then 
                let exp = List.hd exps in
                let sets = Free.free_exp exp in 
                if not (Free.Set.is_empty (sets.varid) || ExpMap.mem exp !acc) then
                  acc := ExpMap.add (List.hd exps) (typ_name ^ bind_suffix ^ string_of_int !acc_i $ no_region, typ_name $ no_region) !acc;
                  acc_i := !acc_i + 1
          | _ -> ()
    end
  in 
  Arg.acc, (module Arg)

let create_mapping_function (id : id) (at : Util.Source.region) (nat_list : nat list) =
  let new_id = (id.it ^ map_func_suffix) $ id.at in
  let new_typ = (NumT `NatT) $ at in
  let user_typ = VarT (id, []) $ at in 
  let new_param = ExpP ("x" $ at, user_typ) $ at in
  
  let empty_tuple = TupE [] $$ at % (TupT [] $ at) in
  let num_exp n = NumE (`Nat n) $$ at % ((NumT `NatT) $ at) in 
  let new_clauses = List.map (fun n -> 
    let mixop = create_mixop at (case_prefix ^ Z.to_string n) in
    let exp = CaseE (mixop, empty_tuple) $$ at % user_typ in
    DefD ([], [ExpA exp $ at], num_exp n, []) $ at
  ) nat_list in
  DecD(new_id, [new_param], new_typ, new_clauses)

let rec transform_type (env : pass_env) (case_map : (id * id) ExpMap.t) (typ : Il.Ast.typ): Il.Ast.typ =
  (match typ.it with
    | VarT (id, args) -> VarT (id, List.map (transform_arg env case_map) args)
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (transform_exp env case_map e, transform_type env case_map t)) exp_typ_pairs)
    | IterT (t, iter) -> IterT (transform_type env case_map t, iter)
    | _ -> typ.it
  ) $ typ.at

and transform_exp (env : pass_env) (case_map : (id * id) ExpMap.t) (exp : exp): exp =
  let t_func = transform_exp env case_map in
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
    | CaseE (m, ({it = TupE exps; _} as e)) -> 
      let id = (Print.string_of_typ_name exp.note) in 
      (match (StringMap.find_opt id env.nat_subs_set) with
        | None -> CaseE (m, transform_exp env case_map e)
        | Some nat_list -> transform_case case_map exps exp nat_list
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
    | UpdE (e1, path, e2) -> UpdE (t_func e1, transform_path env case_map path, t_func e2)
    | ExtE (e1, path, e2) -> ExtE (t_func e1, transform_path env case_map path, t_func e2)
    | CallE (id, args) -> CallE (id, List.map (transform_arg env case_map) args)
    | IterE (e, iterexp) -> IterE (t_func e, transform_iterexp env case_map iterexp)
    | CvtE (e, ntyp1, ntyp2) -> CvtE (t_func e, ntyp1, ntyp2)
    | SubE (e, t1, t2) -> SubE (t_func e, transform_type env case_map t1, transform_type env case_map t2)
    | e -> e
  ) $$ exp.at % (transform_type env case_map exp.note)

and transform_iterexp (env : pass_env) (case_map : (id * id) ExpMap.t) (iterexp : iterexp): iterexp = 
  let (iter, id_exp_pairs) = iterexp in
  (iter, map_snd (transform_exp env case_map) id_exp_pairs)

and transform_case (case_map : (id * id) ExpMap.t) (exps : exp list) (default : exp) (nat_list : nat list): exp' =
  match exps with
    | [{it = NumE (`Nat n); _}] -> 
      if List.mem n nat_list
        then CaseE (create_mixop no_region (case_prefix ^ (Z.to_string n)), empty_tuple) 
        else pass_error default.at ("Cannot monomorphize case that does not exist for nat: " ^ Z.to_string n)
    | [e] when not (Free.Set.is_empty (Free.free_exp e).varid) -> 
      (match (ExpMap.find_opt e case_map) with
        | None -> pass_error default.at "Could not find expression"
        | Some (id, _typ_id) -> VarE id
      )
    | _ -> pass_error default.at "Must have only one expression in case" (* Should not happen due to validation *)
    
and transform_path (env : pass_env) (case_map : (id * id) ExpMap.t) (path : path): path = 
  (match path.it with
    | RootP -> RootP
    | IdxP (p, e) -> IdxP (transform_path env case_map p, transform_exp env case_map e)
    | SliceP (p, e1, e2) -> SliceP (transform_path env case_map p, transform_exp env case_map e1, transform_exp env case_map e2)
    | DotP (p, a) -> DotP (transform_path env case_map p, a)
  ) $$ path.at % transform_type env case_map path.note

and transform_arg (env : pass_env) (case_map : (id * id) ExpMap.t) (arg : arg): arg =
  (match arg.it with
    | ExpA exp -> ExpA (transform_exp env case_map exp)
    | TypA typ -> TypA (transform_type env case_map typ)
    | _ -> arg.it
  ) $ arg.at

and transform_bind (env : pass_env) (case_map : (id * id) ExpMap.t) (bind : bind): bind =
  (match bind.it with
    | ExpB (id, typ) -> ExpB (id, transform_type env case_map typ)
    | b -> b
  ) $ bind.at

and transform_param (env : pass_env) (case_map : (id * id) ExpMap.t) (param : param): param =
  (match param.it with
    | ExpP (id, typ) -> ExpP (id, transform_type env case_map typ)
    | p -> p
  ) $ param.at

and transform_prem (env : pass_env) (case_map : (id * id) ExpMap.t) (prem : prem): prem =
  (match prem.it with
    | IfPr e -> IfPr (transform_exp env case_map e)
    | RulePr (id, m, e) -> RulePr (id, m, transform_exp env case_map e)
    | LetPr (e1, e2, ids) -> LetPr (transform_exp env case_map e1, transform_exp env case_map e2, ids)
    | ElsePr -> ElsePr
    | IterPr (prem, iterexp) -> IterPr (transform_prem env case_map prem, transform_iterexp env case_map iterexp)
  ) $ prem.at

let transform_type_creation (env : pass_env) (id : id) (inst : inst): inst * def' option =
  let (binds, args, deftyp) = get_inst_params inst in 
  let empty_map = ExpMap.empty in
  let reconstruct_typ dtyp opt = (InstD (binds, args, dtyp $ deftyp.at) $ inst.at, opt) in
  match deftyp.it with
    | VariantT [(_, (_, t, [{it = IfPr exp; _}]), _)] when check_nat_type t && check_subset_nat exp -> 
      let nat_list = get_nat_list exp in 
      if nat_list = [] then (inst, None) else
      let new_cases = List.map (fun n ->
        (create_mixop inst.at (case_prefix ^ Z.to_string n), ([], TupT [] $ inst.at, []), [])
      ) nat_list in
      add_to_nat_set env id nat_list;
      reconstruct_typ (VariantT new_cases) (Some (create_mapping_function id inst.at nat_list))
    | VariantT typcases -> reconstruct_typ (VariantT (List.map (fun (m, (binds, t, prems), hints) ->
        (m, (List.map (transform_bind env empty_map) binds, transform_type env empty_map t, List.map (transform_prem env empty_map) prems), hints)
      ) typcases)) None
    | StructT typfields -> reconstruct_typ (StructT (List.map (fun (a, (binds, t, prems), hints) ->
        (a, (List.map (transform_bind env empty_map) binds, transform_type env empty_map t, List.map (transform_prem env empty_map) prems), hints)
      ) typfields)) None
    | AliasT typ -> reconstruct_typ (AliasT (transform_type env ExpMap.empty typ)) None

let transform_rule (env : pass_env) (rule : rule): rule =
  (match rule.it with
    | RuleD (id, binds, m, exp, prems) -> 
      let acc_exps, (module Arg: Iter.Arg) = exp_iter_for_cases env in
      let module Acc = Iter.Make(Arg) in
      Acc.exp exp;
      Acc.prems prems;
      let map_bindings = ExpMap.bindings !acc_exps in
      let new_binds = List.map (fun (_, (id, typ_id)) -> ExpB (id, VarT (typ_id, []) $ no_region) $ no_region) map_bindings in   
      let new_prems = List.map (fun (exp, (id, typ_id)) -> 
        let call_exp = create_nat_call_exp (typ_id.it ^ map_func_suffix $ no_region) [ExpA (create_var_exp id typ_id) $ no_region] in 
        IfPr (create_cmp call_exp exp) $ no_region
      ) map_bindings in
      RuleD (id, List.map (transform_bind env !acc_exps) binds @ new_binds, m, 
        transform_exp env !acc_exps exp, 
        List.map (transform_prem env !acc_exps) prems @ new_prems)
  ) $ rule.at

let transform_clause (env : pass_env) (clause : clause): clause =
  (match clause.it with
    | DefD (binds, args, exp, prems) -> 
      let acc_exps, (module Arg: Iter.Arg) = exp_iter_for_cases env in
      let module Acc = Iter.Make(Arg) in
      Acc.args args;
      Acc.exp exp;
      Acc.prems prems;
      let map_bindings = ExpMap.bindings !acc_exps in
      let new_binds = List.map (fun (_, (id, typ_id)) -> ExpB (id, VarT (typ_id, []) $ no_region) $ no_region) map_bindings in
      let new_prems = List.map (fun (exp, (id, typ_id)) ->
        let call_exp = create_nat_call_exp (typ_id.it ^ map_func_suffix $ no_region) [ExpA (create_var_exp id typ_id) $ no_region] in 
        IfPr (create_cmp call_exp exp) $ no_region
      ) map_bindings in
      DefD (List.map (transform_bind env !acc_exps) binds @ new_binds, 
        List.map (transform_arg env !acc_exps) args, 
        transform_exp env !acc_exps exp, List.map (transform_prem env !acc_exps) prems @ new_prems)
  ) $ clause.at

let rec transform_def (env : pass_env) (def : def): def list = 
  (match def.it with
    | TypD (id, params, insts) -> let (new_insts, opts) = List.split (List.map (transform_type_creation env id) insts) in
      [TypD (id, List.map (transform_param env ExpMap.empty) params, new_insts)] @ List.filter_map (fun d -> d) opts
    | RelD (id, mixop, typ, rules) -> [RelD (id, mixop, transform_type env ExpMap.empty typ, List.map (transform_rule env) rules)]
    | DecD (id, params, typ, clauses) -> [DecD (id, List.map (transform_param env ExpMap.empty) params, transform_type env ExpMap.empty typ, List.map (transform_clause env) clauses)]
    | RecD defs -> [RecD (List.concat_map (transform_def env) defs)]
    | _ -> [def.it]
  ) |> List.map (fun d' -> d' $ def.at)

let transform (script : script) =
  let pass_env = empty_pass_env in 
  List.concat_map (transform_def pass_env) script