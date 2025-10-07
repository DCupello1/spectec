open Il.Ast
open Il
open Util.Source

module StringMap = Map.Make(String)
module IntSet = Set.Make(Int)
type uncase_map = (IntSet.t) StringMap.t

type env = {
  mutable uncase_map : uncase_map;
  mutable env : Il.Env.t;
}

let empty_env = {
  uncase_map = StringMap.empty;
  env = Il.Env.empty
}

let var_prefix = "v_"
let proj_prefix = "proj_"

let get_case_typs t = 
  match t.it with
  | TupT typs -> typs
  | _ -> [(VarE ("_" $ t.at) $$ t.at % t, t)]

let iter_name i = 
  match i with
  | Opt -> "opt"
  | List | List1 | ListN _ -> "list"

let rec typ_name t =
  match t.it with
  | VarT (id, _) -> id.it
  | BoolT -> "bool"
  | NumT _ -> "num"
  | TextT -> "str"
  | TupT pairs -> String.concat "__" (List.map (fun (_, t) -> typ_name t) pairs) ^ "_pair"
  | IterT (typ, iter) -> typ_name typ ^ "_" ^ iter_name iter 

let make_arg p = 
  (match p.it with
  | ExpP (id, typ) -> ExpA (VarE id $$ id.at % typ) 
  | TypP id -> TypA (VarT (id, []) $ id.at) (* TODO unsure this makes sense*)
  | DefP (id, _, _) -> DefA id 
  | GramP (_, _) -> assert false (* Avoid this *)
  ) $ p.at

let make_bind p = 
  (match p.it with 
  | ExpP (id, typ) -> ExpB (id, typ)
  | TypP id -> TypB id
  | DefP (id, params, typ) -> DefB (id, params, typ)
  | GramP _ -> assert false (* Avoid this *)
  ) $ p.at

let create_projection_functions id params int_set inst =
  let get_deftyp inst' = (match inst'.it with
    | InstD (_binds, _args, deftyp) -> deftyp.it
  ) in 
  let at = inst.at in 
  let user_typ = VarT (id, List.map make_arg params) $ at in 
  let new_param = ExpP ("x" $ at, user_typ) $ at in
  let make_func m case_typs n = 
    let new_params = params @ [new_param] in 
    let new_var_exps = List.mapi (fun idx (_, t) -> VarE (var_prefix ^ typ_name t ^ "_" ^ Int.to_string idx $ at) $$ at % t) case_typs in 
    let new_tup = TupE (new_var_exps) $$ at % (TupT case_typs $ at) in
    let new_case_exp = CaseE(m, new_tup) $$ at % user_typ in
    let new_arg = ExpA new_case_exp $ at in 
    let new_binds = List.mapi (fun idx (_, t) -> ExpB (var_prefix ^ typ_name t ^ "_" ^ Int.to_string idx $ at, t) $ at) case_typs in
    DecD ((proj_prefix ^ id.it ^ "_" ^ Int.to_string n) $ id.at, new_params, snd (List.nth case_typs n), 
    [DefD (List.map make_bind params @ new_binds, List.map make_arg params @ [new_arg], List.nth new_var_exps n, []) $ at]
  )
  in

  List.map (fun n -> 
    (match (get_deftyp inst) with
    | AliasT _typ -> assert false (* Give appropriate error, should not happen due to reduction *)
    | StructT _ -> assert false (* Give appropriate error, should not be allowed *)
    | VariantT [(m, (_, typ, _), _)] -> 
      let case_typs = get_case_typs typ in
      if n >= List.length case_typs then assert false else
      make_func m case_typs n
    | _ -> assert false
    )
  ) (IntSet.elements int_set)

let rec preprocess_iter p_env i =
  match i with 
  | ListN (exp, id_opt) -> ListN (preprocess_exp p_env exp, id_opt)
  | _ -> i

and preprocess_typ p_env t = 
  (match t.it with
  | VarT (id, args) -> VarT (id, List.map (preprocess_arg p_env) args)
  | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (preprocess_exp p_env e, preprocess_typ p_env t)) exp_typ_pairs)
  | IterT (typ, iter) -> IterT (preprocess_typ p_env typ, preprocess_iter p_env iter)
  | typ -> typ
  ) $ t.at

and preprocess_exp p_env e = 
  let p_func = preprocess_exp p_env in
  (match e.it with
  | ProjE ({ it = UncaseE(e, _); _}, n) -> 
    (* Supplying the projection function for UncaseE removal *)
    let typ = Eval.reduce_typ p_env.env e.note in 
    let typ_name = Print.string_of_typ_name typ in
    let args = (match typ.it with 
      | VarT (_, args) -> args
      | _ -> assert false (* TODO appropriate error for this *)
    ) in CallE (proj_prefix ^ typ_name ^ "_" ^ Int.to_string n $ no_region, List.map (preprocess_arg p_env) (args @ [ExpA e $ e.at]))
  | CaseE (m, e1) -> CaseE (m, p_func e1)
  | StrE fields -> StrE (List.map (fun (a, e1) -> (a, p_func e1)) fields)
  | UnE (unop, optyp, e1) -> UnE (unop, optyp, p_func e1)
  | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, p_func e1, p_func e2)
  | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, p_func e1, p_func e2)
  | TupE (exps) -> TupE (List.map p_func exps)
  | ProjE (e1, n) -> ProjE (p_func e1, n)
  | UncaseE (e1, m) -> UncaseE (p_func e1, m)
  | OptE e1 -> OptE (Option.map p_func e1)
  | TheE e1 -> TheE (p_func e1)
  | DotE (e1, a) -> DotE (p_func e1, a)
  | CompE (e1, e2) -> CompE (p_func e1, p_func e2)
  | ListE entries -> ListE (List.map p_func entries)
  | LiftE e1 -> LiftE (p_func e1)
  | MemE (e1, e2) -> MemE (p_func e1, p_func e2)
  | LenE e1 -> LenE e1
  | CatE (e1, e2) -> CatE (p_func e1, p_func e2)
  | IdxE (e1, e2) -> IdxE (p_func e1, p_func e2)
  | SliceE (e1, e2, e3) -> SliceE (p_func e1, p_func e2, p_func e3)
  | UpdE (e1, p, e2) -> UpdE (p_func e1, preprocess_path p_env p, p_func e2)
  | ExtE (e1, p, e2) -> ExtE (p_func e1, preprocess_path p_env p, p_func e2)
  | CallE (id, args) -> CallE (id, List.map (preprocess_arg p_env) args)
  | IterE (e1, (iter, id_exp_pairs)) -> IterE (p_func e1, (preprocess_iter p_env iter, List.map (fun (id, exp) -> (id, p_func exp)) id_exp_pairs))
  | CvtE (e1, nt1, nt2) -> CvtE (p_func e1, nt1, nt2)
  | SubE (e1, t1, t2) -> SubE (p_func e1, preprocess_typ p_env t1, preprocess_typ p_env t2)
  | exp -> exp
  ) $$ e.at % (preprocess_typ p_env e.note)

and preprocess_path p_env path = 
  (match path.it with
  | RootP -> RootP
  | IdxP (p, e) -> IdxP (preprocess_path p_env p, preprocess_exp p_env e)
  | SliceP (p, e1, e2) -> SliceP (preprocess_path p_env p, preprocess_exp p_env e1, preprocess_exp p_env e2)
  | DotP (p, a) -> DotP (preprocess_path p_env p, a)
  ) $$ path.at % (preprocess_typ p_env path.note)

and preprocess_sym p_env s = 
  (match s.it with
  | VarG (id, args) -> VarG (id, List.map (preprocess_arg p_env) args)
  | SeqG syms | AltG syms -> SeqG (List.map (preprocess_sym p_env) syms)
  | RangeG (syml, symu) -> RangeG (preprocess_sym p_env syml, preprocess_sym p_env symu)
  | IterG (sym, (iter, id_exp_pairs)) -> IterG (preprocess_sym p_env sym, (preprocess_iter p_env iter, 
      List.map (fun (id, exp) -> (id, preprocess_exp p_env exp)) id_exp_pairs)
    )
  | AttrG (e, sym) -> AttrG (preprocess_exp p_env e, preprocess_sym p_env sym)
  | sym -> sym 
  ) $ s.at 

and preprocess_arg p_env a =
  (match a.it with
  | ExpA exp -> ExpA (preprocess_exp p_env exp)
  | TypA typ -> TypA (preprocess_typ p_env typ)
  | DefA id -> DefA id
  | GramA sym -> GramA (preprocess_sym p_env sym)
  ) $ a.at

and preprocess_bind p_env b =
  (match b.it with
  | ExpB (id, typ) -> ExpB (id, preprocess_typ p_env typ)
  | TypB id -> TypB id
  | DefB (id, params, typ) -> DefB (id, List.map (preprocess_param p_env) params, preprocess_typ p_env typ)
  | GramB (id, params, typ) -> GramB (id, List.map (preprocess_param p_env) params, preprocess_typ p_env typ)
  ) $ b.at 
  
and preprocess_param p_env p =
  (match p.it with
  | ExpP (id, typ) -> ExpP (id, preprocess_typ p_env typ)
  | TypP id -> TypP id
  | DefP (id, params, typ) -> DefP (id, List.map (preprocess_param p_env) params, preprocess_typ p_env typ)
  | GramP (id, typ) -> GramP (id, preprocess_typ p_env typ)
  ) $ p.at 

let rec preprocess_prem p_env prem = 
  (match prem.it with
  | RulePr (id, m, e) -> RulePr (id, m, preprocess_exp p_env e)
  | IfPr e -> IfPr (preprocess_exp p_env e)
  | LetPr (e1, e2, ids) -> LetPr (preprocess_exp p_env e1, preprocess_exp p_env e2, ids)
  | ElsePr -> ElsePr
  | IterPr (prem1, (iter, id_exp_pairs)) -> IterPr (preprocess_prem p_env prem1, 
      (preprocess_iter p_env iter, List.map (fun (id, exp) -> (id, preprocess_exp p_env exp)) id_exp_pairs)
    )
  | NegPr p -> NegPr p
  ) $ prem.at

let preprocess_inst p_env inst = 
  (match inst.it with
  | InstD (binds, args, deftyp) -> InstD (List.map (preprocess_bind p_env) binds, List.map (preprocess_arg p_env) args, 
    (match deftyp.it with 
    | AliasT typ -> AliasT (preprocess_typ p_env typ)
    | StructT typfields -> StructT (List.map (fun (a, (c_binds, typ, prems), hints) ->
        (a, (List.map (preprocess_bind p_env) c_binds, preprocess_typ p_env typ, List.map (preprocess_prem p_env) prems), hints)  
      ) typfields)
    | VariantT typcases -> 
      VariantT (List.map (fun (m, (c_binds, typ, prems), hints) -> 
        (m, (List.map (preprocess_bind p_env) c_binds, preprocess_typ p_env typ, List.map (preprocess_prem p_env) prems), hints)  
      ) typcases)
    ) $ deftyp.at
  )
  ) $ inst.at

let preprocess_rule p_env rule = 
  (match rule.it with
  | RuleD (id, binds, m, exp, prems) -> RuleD (id.it $ no_region, 
    List.map (preprocess_bind p_env) binds, 
    m, 
    preprocess_exp p_env exp, 
    List.map (preprocess_prem p_env) prems
  )
  ) $ rule.at

let preprocess_clause p_env clause =
  (match clause.it with 
  | DefD (binds, args, exp, prems) -> DefD (List.map (preprocess_bind p_env) binds, 
    List.map (preprocess_arg p_env) args,
    preprocess_exp p_env exp, 
    List.map (preprocess_prem p_env) prems
  )
  ) $ clause.at

let preprocess_prod p_env prod = 
  (match prod.it with 
  | ProdD (binds, sym, exp, prems) -> ProdD (List.map (preprocess_bind p_env) binds,
    preprocess_sym p_env sym,
    preprocess_exp p_env exp,
    List.map (preprocess_prem p_env) prems
  )
  ) $ prod.at

let rec preprocess_def p_env def = 
  (match def.it with
  | TypD (id, params, [inst]) -> 
    let d = TypD (id, List.map (preprocess_param p_env) params, [preprocess_inst p_env inst]) in 
    (match (StringMap.find_opt id.it p_env.uncase_map) with 
      | None -> [d]
      | Some int_set -> d :: create_projection_functions id params int_set inst
    )
  | TypD (id, params, insts) -> 
    [TypD (id, List.map (preprocess_param p_env) params, List.map (preprocess_inst p_env) insts)]
  | RelD (id, m, typ, rules) -> 
    [RelD (id, m, preprocess_typ p_env typ, List.map (preprocess_rule p_env) rules)]
  | DecD (id, params, typ, clauses) -> [DecD (id, List.map (preprocess_param p_env) params, preprocess_typ p_env typ, List.map (preprocess_clause p_env) clauses)]
  | GramD (id, params, typ, prods) -> [GramD (id, List.map (preprocess_param p_env) params, preprocess_typ p_env typ, List.map (preprocess_prod p_env) prods)]
  | RecD defs -> [RecD (List.concat_map (preprocess_def p_env) defs)]
  | HintD hintdef -> [HintD hintdef]
  ) |> List.map (fun d -> d $ def.at)

let collect_uncase_iter env: uncase_map ref * (module Iter.Arg) =
  let module Arg = 
    struct
      include Iter.Skip 
      let acc = ref StringMap.empty
      let visit_exp (exp : exp) = 
        match exp.it with
        | ProjE ({ it = UncaseE(e, _); _}, n) -> 
          let typ_name = Print.string_of_typ_name (Il.Eval.reduce_typ env e.note) in
          acc := StringMap.update typ_name (fun int_set_opt -> match int_set_opt with 
            | None -> Some (IntSet.singleton n)
            | Some int_set -> Some (IntSet.add n int_set)
          ) !acc
        | _ -> ()
    end
  in Arg.acc, (module Arg)

let transform (il : script): script =
  let p_env = empty_env in 
  p_env.env <- Il.Env.env_of_script il;

  (* Building up uncase_map *)
  let acc, (module Arg : Iter.Arg) = collect_uncase_iter p_env.env in
  let module Acc = Iter.Make(Arg) in
  List.iter Acc.def il;
  p_env.uncase_map <- !acc;

  (* Main transformation *)
  
  List.concat_map (preprocess_def p_env) il 