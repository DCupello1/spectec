open Il.Ast
open Util.Source
open Util.Error

module StringMap = Map.Make(String)

type wf_entry = 
  | NormalType
  | ExtraType

type env = {
  mutable wf_map : wf_entry StringMap.t;
  mutable il_env : Il.Env.t;
}

let empty_env = {
  wf_map = StringMap.empty;
  il_env = Il.Env.empty
}
let var_name = "var_x" 
let extra_name = "v"
let wf_pred_prefix = "wf_"

let rule_prefix = "case_"

let _error at msg = error at "Undep error" msg


let _get_case_typs t = 
  match t.it with
  | TupT typs -> typs
  | _ -> [(VarE ("_" $ t.at) $$ t.at % t, t)]

let _iter_name i = 
  match i with
  | Opt -> "opt"
  | List | List1 | ListN _ -> "list"


let _make_arg p = 
  (match p.it with
  | ExpP (id, typ) -> ExpA (VarE id $$ id.at % typ) 
  | TypP id -> TypA (VarT (id, []) $ id.at) (* TODO unsure this makes sense*)
  | DefP (id, _, _) -> DefA id 
  | GramP (_, _) -> assert false (* Avoid this *)
  ) $ p.at

let _make_bind p = 
  (match p.it with 
  | ExpP (id, typ) -> ExpB (id, typ)
  | TypP id -> TypB id
  | DefP (id, params, typ) -> DefB (id, params, typ)
  | GramP _ -> assert false (* Avoid this *)
  ) $ p.at

let is_type_arg arg = 
  match arg.it with
  | TypA _ -> true
  | _ -> false

let is_type_param param =
  match param.it with
  | TypP _ -> true
  | _ -> false

let is_type_bind bind = 
  match bind.it with
  | TypB _ -> true
  | _ -> false

let rec transform_iter env i =
  match i with 
  | ListN (exp, id_opt) -> ListN (transform_exp env exp, id_opt)
  | _ -> i

and transform_typ env t = 
  (match t.it with
  | VarT (id, args) -> VarT (id, List.filter is_type_arg (List.map (transform_arg env) args))
  | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (transform_exp env e, transform_typ env t)) exp_typ_pairs)
  | IterT (typ, iter) -> IterT (transform_typ env typ, transform_iter env iter)
  | typ -> typ
  ) $ t.at

and transform_exp env e = 
  let t_func = transform_exp env in
  (match e.it with
  | CaseE (m, e1) -> CaseE (m, t_func e1)
  | StrE fields -> StrE (List.map (fun (a, e1) -> (a, t_func e1)) fields)
  | UnE (unop, optyp, e1) -> UnE (unop, optyp, t_func e1)
  | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2)
  | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2)
  | TupE (exps) -> TupE (List.map t_func exps)
  | ProjE (e1, n) -> ProjE (t_func e1, n)
  | UncaseE (e1, m) -> UncaseE (t_func e1, m)
  | OptE e1 -> OptE (Option.map t_func e1)
  | TheE e1 -> TheE (t_func e1)
  | DotE (e1, a) -> DotE (t_func e1, a)
  | CompE (e1, e2) -> CompE (t_func e1, t_func e2)
  | ListE entries -> ListE (List.map t_func entries)
  | LiftE e1 -> LiftE (t_func e1)
  | MemE (e1, e2) -> MemE (t_func e1, t_func e2)
  | LenE e1 -> LenE e1
  | CatE (e1, e2) -> CatE (t_func e1, t_func e2)
  | IdxE (e1, e2) -> IdxE (t_func e1, t_func e2)
  | SliceE (e1, e2, e3) -> SliceE (t_func e1, t_func e2, t_func e3)
  | UpdE (e1, p, e2) -> UpdE (t_func e1, transform_path env p, t_func e2)
  | ExtE (e1, p, e2) -> ExtE (t_func e1, transform_path env p, t_func e2)
  | CallE (id, args) -> CallE (id, List.map (transform_arg env) args)
  | IterE (e1, (iter, id_exp_pairs)) -> IterE (t_func e1, (transform_iter env iter, List.map (fun (id, exp) -> (id, t_func exp)) id_exp_pairs))
  | CvtE (e1, nt1, nt2) -> CvtE (t_func e1, nt1, nt2)
  | SubE (e1, t1, t2) -> SubE (t_func e1, transform_typ env t1, transform_typ env t2)
  | exp -> exp
  ) $$ e.at % (transform_typ env e.note)

and transform_path env path = 
  (match path.it with
  | RootP -> RootP
  | IdxP (p, e) -> IdxP (transform_path env p, transform_exp env e)
  | SliceP (p, e1, e2) -> SliceP (transform_path env p, transform_exp env e1, transform_exp env e2)
  | DotP (p, a) -> DotP (transform_path env p, a)
  ) $$ path.at % (transform_typ env path.note)

and transform_sym env s = 
  (match s.it with
  | VarG (id, args) -> VarG (id, List.map (transform_arg env) args)
  | SeqG syms | AltG syms -> SeqG (List.map (transform_sym env) syms)
  | RangeG (syml, symu) -> RangeG (transform_sym env syml, transform_sym env symu)
  | IterG (sym, (iter, id_exp_pairs)) -> IterG (transform_sym env sym, (transform_iter env iter, 
      List.map (fun (id, exp) -> (id, transform_exp env exp)) id_exp_pairs)
    )
  | AttrG (e, sym) -> AttrG (transform_exp env e, transform_sym env sym)
  | sym -> sym 
  ) $ s.at 

and transform_arg env a =
  (match a.it with
  | ExpA exp -> ExpA (transform_exp env exp)
  | TypA typ -> TypA (transform_typ env typ)
  | DefA id -> DefA id
  | GramA sym -> GramA (transform_sym env sym)
  ) $ a.at

and transform_bind env b =
  (match b.it with
  | ExpB (id, typ) -> ExpB (id, transform_typ env typ)
  | TypB id -> TypB id
  | DefB (id, params, typ) -> DefB (id, List.map (transform_param env) params, transform_typ env typ)
  | GramB (id, params, typ) -> GramB (id, List.map (transform_param env) params, transform_typ env typ)
  ) $ b.at 
  
and transform_param env p =
  (match p.it with
  | ExpP (id, typ) -> ExpP (id, transform_typ env typ)
  | TypP id -> TypP id
  | DefP (id, params, typ) -> DefP (id, List.map (transform_param env) params, transform_typ env typ)
  | GramP (id, typ) -> GramP (id, transform_typ env typ)
  ) $ p.at 

let rec transform_prem env prem = 
  (match prem.it with
  | RulePr (id, m, e) -> RulePr (id, m, transform_exp env e)
  | IfPr e -> IfPr (transform_exp env e)
  | LetPr (e1, e2, ids) -> LetPr (transform_exp env e1, transform_exp env e2, ids)
  | ElsePr -> ElsePr
  | IterPr (prem1, (iter, id_exp_pairs)) -> IterPr (transform_prem env prem1, 
      (transform_iter env iter, List.map (fun (id, exp) -> (id, transform_exp env exp)) id_exp_pairs)
    )
  | NegPr p -> NegPr p
  ) $ prem.at

let transform_inst env inst = 
  (match inst.it with
  | InstD (binds, args, deftyp) -> InstD (List.map (transform_bind env) binds |> List.filter is_type_bind, List.map (transform_arg env) args |> List.filter is_type_arg, 
    (match deftyp.it with 
    | AliasT typ -> AliasT (transform_typ env typ)
    | StructT typfields -> StructT (List.map (fun (a, (c_binds, typ, _prems), hints) ->
        (a, (List.map (transform_bind env) c_binds, transform_typ env typ, []), hints)  
      ) typfields)
    | VariantT typcases -> 
      VariantT (List.map (fun (m, (c_binds, typ, _prems), hints) -> 
        (m, (List.map (transform_bind env) c_binds, transform_typ env typ, []), hints)  
      ) typcases)
    ) $ deftyp.at
  )
  ) $ inst.at


let create_well_formed_predicate id _env inst = 
  let get_tuple_typ t =
    match t.it with
    | TupT tups -> tups
    | _ -> [(VarE (extra_name $ id.at) $$ id.at % t, t)]
  in
  let at = id.at in 
  match inst.it with
  | InstD (binds, _args, {it = VariantT typcases; _}) -> 
    let user_typ = VarT(id, []) $ at in
    let new_bind = ExpB (var_name $ at, user_typ) $ at in
    let _new_binds = binds @ [new_bind] in 
    let dep_exp_typ_pairs = List.filter_map (fun b -> match b.it with 
      | ExpB (id', typ) -> Some ((VarE id' $$ id'.at % typ, typ))
      | _ -> None
    ) binds in
    let pairs_without_names = List.filter_map (fun b -> match b.it with 
      | ExpB (id', typ) -> Some ((VarE ("_" $ id'.at) $$ id'.at % typ, typ))
      | _ -> None
    ) binds in
    let tupt = TupT (pairs_without_names @ [(VarE ("_" $ at) $$ at % user_typ, user_typ)]) $ at in
    let new_mixop = [] :: List.init (List.length dep_exp_typ_pairs + 1) (fun _ -> []) in
    let _a = NormalType in
    let _b = ExtraType in
    let rules = List.mapi (fun i (m, (case_binds, case_typ, prems), _) ->
      let exp_typ_pairs = get_tuple_typ case_typ in 

      let exp = TupE (List.map fst exp_typ_pairs) $$ at % (TupT exp_typ_pairs $ no_region) in 
      let case_exp = CaseE (m, exp) $$ at % user_typ in
      let tuple_exp = TupE (List.map fst dep_exp_typ_pairs @ [case_exp]) $$ at % tupt in
      RuleD (id.it ^ "_" ^ rule_prefix ^ Int.to_string i $ no_region, binds @ case_binds, new_mixop, tuple_exp, prems) $ no_region
    ) typcases |> List.filter (fun rule -> match rule.it with
      RuleD (_, _, _, _, prems) -> prems <> []
    )
    in

    if rules = [] then None else 
    let relation = RelD (wf_pred_prefix ^ id.it $ id.at, new_mixop, tupt, rules) in 
    Some relation
  | _ -> None

let transform_rule env rule = 
  (match rule.it with
  | RuleD (id, binds, m, exp, prems) -> RuleD (id.it $ no_region, 
    List.map (transform_bind env) binds, 
    m, 
    transform_exp env exp, 
    List.map (transform_prem env) prems
  )
  ) $ rule.at

let transform_clause env clause =
  (match clause.it with 
  | DefD (binds, args, exp, prems) -> DefD (List.map (transform_bind env) binds, 
    List.map (transform_arg env) args,
    transform_exp env exp, 
    List.map (transform_prem env) prems
  )
  ) $ clause.at

let transform_prod env prod = 
  (match prod.it with 
  | ProdD (binds, sym, exp, prems) -> ProdD (List.map (transform_bind env) binds,
    transform_sym env sym,
    transform_exp env exp,
    List.map (transform_prem env) prems
  )
  ) $ prod.at

let is_not_exp_param param =
  match param.it with
    | ExpP _ -> false
    | _ -> true

let rec transform_def env def = 
  (match def.it with
  | TypD (id, params, [inst]) when List.exists is_not_exp_param params -> 
    [TypD (id, List.map (transform_param env) params |> List.filter is_type_param, [inst])]
  | TypD (id, params, [inst]) -> 
    let relation = Option.to_list (create_well_formed_predicate id env inst) in
    TypD (id, List.map (transform_param env) params |> List.filter is_type_param, [transform_inst env inst]) :: relation
  | TypD (_, _, _) -> 
    [def.it]
    (* error def.at "Multiples instances encountered, please run type family removal pass first." *)
  | RelD (id, m, typ, rules) -> 
    [RelD (id, m, transform_typ env typ, List.map (transform_rule env) rules)]
  | DecD (id, params, typ, clauses) -> [DecD (id, List.map (transform_param env) params, transform_typ env typ, List.map (transform_clause env) clauses)]
  | GramD (id, params, typ, prods) -> [GramD (id, List.map (transform_param env) params, transform_typ env typ, List.map (transform_prod env) prods)]
  | RecD defs -> [RecD (List.concat_map (transform_def env) defs)]
  | HintD hintdef -> [HintD hintdef]
  ) |> List.map (fun d -> d $ def.at)
let transform (il : script): script =
  let env = empty_env in 
  env.il_env <- Il.Env.env_of_script il;
  List.concat_map (transform_def env) il 