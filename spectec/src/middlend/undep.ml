open Il.Ast
open Util.Source
open Util.Error
open Il

module StringSet = Set.Make(String)

type env = {
  mutable wf_set : StringSet.t;
  mutable il_env : Il.Env.t;
}

let empty_env = {
  wf_set = StringSet.empty;
  il_env = Il.Env.empty
}

let _var_name = "var_x" 
let wf_pred_prefix = "wf_"
let rule_prefix = "case_"

let error at msg = error at "Undep error" msg

let rec split3concat = function
    [] -> ([], [], [])
  | (x,y, z)::l ->
      let (rx, ry, rz) = split3concat l in (x @ rx, y @ ry, z @ rz)

let remove_last_char s =
  if not (String.ends_with ~suffix:"*" s || String.ends_with ~suffix:"?" s) then s else  
  let len = String.length s in
  if len = 0 then s
  else String.sub s 0 (len - 1)

let generate_var at ids id =
  let start = 0 in
  let fresh_prefix = "var" in
  let max = 100 in
  let rec go c =
    if max <= c then error at "Reached max variable generation" else
    let name = fresh_prefix ^ "_" ^ Int.to_string c in 
    if (List.mem name ids) 
      then go (c + 1) 
      else name
  in
  match id with
  | "" | "_" -> go start
  | _ -> id

let improve_ids_binders generate_binds at exp_typ_pairs =
  let get_id_from_exp e = 
    match e.it with
    | VarE id -> Some id.it
    | _ -> None
  in
  let rec improve_ids_helper ids bs = 
    match bs with
    | [] -> ([], [])
    | ({it = VarE b_id; _}, t) :: bs' -> 
      let new_name = generate_var at ids b_id.it in 
      let (binds, pairs) = improve_ids_helper (new_name :: ids) bs' in
      let new_pairs = (VarE (new_name $ b_id.at) $$ b_id.at % t, t) :: pairs in 
      if (not generate_binds) && new_name = b_id.it
        then (binds, new_pairs)
        else ((ExpB (new_name $ b_id.at, t) $ at) :: binds, new_pairs)
    | ({it = TupE exps; at = exp_at; _}, {it = TupT exp_typ_pairs'; at = typ_at; _}) :: bs'  when List.length exps = List.length exp_typ_pairs' -> 
      let typs = List.map snd exp_typ_pairs' in
      let (binds, pairs) = improve_ids_helper ids (List.combine exps typs) in
      let new_ids = List.filter_map get_id_from_exp (List.map fst pairs) in 
      let (binds', pairs') = improve_ids_helper (new_ids @ ids) bs' in
      let tupt = TupT pairs $ typ_at in
      let tupe = TupE (List.map fst pairs) $$ exp_at % tupt in 
      (binds' @ binds, (tupe, tupt) :: pairs')
    | b :: bs' -> 
      let (binds, pairs) = improve_ids_helper ids bs' in
      (binds, b :: pairs)
  in
  improve_ids_helper [] exp_typ_pairs

let check_normal_type_creation (inst : inst) : bool = 
  match inst.it with
  | InstD (_, args, _) -> List.for_all (fun arg -> 
    match arg.it with 
    (* Args in normal types can really only be variable expressions or type params *)
    | ExpA {it = VarE _; _} | TypA _ -> true
    | _ -> false  
    ) args 

let rec reduce_type_aliasing env t =
  match t.it with
  | VarT(id, args) -> 
    (match Env.find_opt_typ env id with 
    | Some (_, [inst]) when check_normal_type_creation inst -> reduce_inst_alias env args inst t
    | _ -> t
    )
  | _ -> t

and reduce_inst_alias env args inst base_typ = 
  match inst.it with
  | InstD (_, args', {it = AliasT typ; _}) ->
    let subst_opt = Eval.match_list Eval.match_arg env Subst.empty args args' in
    (match subst_opt with
    | Some subst -> reduce_type_aliasing env (Subst.subst_typ subst typ)
    | None -> reduce_type_aliasing env typ
    ) 
  | _ -> base_typ

let bind_wf_set env id =
  if id <> "" && id <> "_" then
  env.wf_set <- StringSet.add id env.wf_set

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
  ) $$ e.at % transform_typ env e.note

and transform_path env path = 
  (match path.it with
  | RootP -> RootP
  | IdxP (p, e) -> IdxP (transform_path env p, transform_exp env e)
  | SliceP (p, e1, e2) -> SliceP (transform_path env p, transform_exp env e1, transform_exp env e2)
  | DotP (p, a) -> DotP (transform_path env p, a)
  ) $$ path.at % transform_typ env path.note

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
  )) $ inst.at

let needs_wfness env def = 
  match def.it with
  | TypD (_, _, [{it = InstD (binds, _, deftyp); _}]) ->
    let prems_list = match deftyp.it with
    | StructT typfields -> List.map (fun (_, (_, _, prems), _) -> prems) typfields
    | VariantT typcases -> List.map (fun (_, (_, _, prems), _) -> prems) typcases
    | _ -> []
    in
    List.exists (fun b -> match b.it with
      | ExpB (id, _) -> StringSet.mem id.it env.wf_set
      | _ -> false 
    ) binds ||
    List.exists (fun prems -> prems <> []) prems_list
  | _ -> false

let rec get_wf_pred env (exp, t) = 
  let get_id exp =
    match exp.it with
    | VarE id -> id
    | _ -> 
      (* This should never happen as long as the code doesn't change *)
      error exp.at ("Abnormal bind - does not have correct exp: " ^ Il.Print.string_of_exp exp)
  in
  let t' = reduce_type_aliasing env.il_env t in
  let exp' = {exp with note = t'} in 
  match t'.it with
    | VarT (id, args) when StringSet.mem id.it env.wf_set ->
      let new_mixop = [] :: List.init (List.length args + 1) (fun _ -> []) in
      let exp_args = List.filter_map (fun a -> match a.it with 
        | ExpA exp -> Some exp
        | _ -> None
      ) args in
      let tupt = TupT (List.map (fun e -> (VarE ("" $ id.at) $$ id.at % e.note), e.note) exp_args) $ id.at in
      let tuple_exp = TupE (exp_args @ [exp']) $$ id.at % tupt in
      [RulePr (wf_pred_prefix ^ id.it $ id.at, new_mixop, tuple_exp) $ id.at]
    | IterT (typ, iter) ->
      let name = get_id exp' in
      let name' = remove_last_char name.it $ name.at in 
      let prems = get_wf_pred env (VarE name' $$ name.at % typ, typ) in
      List.map (fun prem -> IterPr (prem, (iter, [(name', exp')])) $ name.at) prems
    | TupT exp_typ_pairs -> 
      let prems = 
        List.mapi (fun idx (_, typ) -> 
          get_wf_pred env (ProjE (exp', idx) $$ exp.at % typ, typ)) exp_typ_pairs |> 
        List.concat 
      in
      prems
    | _ -> []

let rec non_empty_var e = 
  match e.it with
  | VarE id -> id.it <> "" && id.it <> "_"
  | IterE (e, _) -> non_empty_var e 
  | TupE exps -> List.exists non_empty_var exps
  | _ -> false

let create_well_formed_predicate id env inst = 
  let get_exp_typ b = 
    match b.it with
    | ExpB (id, typ) -> Some (VarE id $$ id.at % typ, typ)
    | _ -> None
  in
  let at = id.at in 
  let user_typ = VarT(id, []) $ at in
  match inst.it with
  (* Variant well formedness predicate creation *)
  | InstD (binds, _args, {it = VariantT typcases; _}) -> 
    let pairs_without_names, dep_exp_typ_pairs = List.split (List.filter_map (fun b -> match b.it with 
      | ExpB (id', typ) -> Some ((VarE ("_" $ id'.at) $$ id'.at % typ, typ), (VarE id' $$ id'.at % typ, typ))
      | _ -> None
    ) binds) in
    let tupt = TupT (pairs_without_names @ [(VarE ("_" $ at) $$ at % user_typ, user_typ)]) $ at in
    let new_mixop = [] :: List.init (List.length dep_exp_typ_pairs + 1) (fun _ -> []) in
    let rules = List.mapi (fun i (m, (case_binds, case_typ, prems), _) ->
      let exp_typ_pairs = match case_typ.it with
        | TupT tups -> tups
        | _ -> [(VarE ("_" $ id.at) $$ id.at % case_typ, case_typ)] 
      in 
      let extra_binds, t_pairs = improve_ids_binders false id.at exp_typ_pairs in
      let new_binds = case_binds @ extra_binds in 
      let exp = TupE (List.map fst t_pairs) $$ at % (TupT t_pairs $ at) in 
      let case_exp = CaseE (m, exp) $$ at % user_typ in
      let tuple_exp = TupE (List.map fst dep_exp_typ_pairs @ [case_exp]) $$ at % tupt in
      let extra_prems = List.filter_map get_exp_typ new_binds |> List.concat_map (get_wf_pred env) in
      RuleD (id.it ^ "_" ^ rule_prefix ^ Int.to_string i $ at, 
        List.map (transform_bind env) (binds @ new_binds), new_mixop, 
        transform_exp env tuple_exp, 
        List.map (transform_prem env) (extra_prems @ prems)
      ) $ at
    ) typcases
    in
    let has_no_prems = List.for_all (fun rule -> match rule.it with
      | RuleD (_, _, _, _, prems) -> prems = []   
    ) rules in
    if has_no_prems then None else 
    let relation = RelD (wf_pred_prefix ^ id.it $ id.at, new_mixop, tupt, rules) $ at in 
    bind_wf_set env id.it;
    Some relation

  (* Struct/Record well formedness predicate creation *)
  | InstD (binds, _args, {it = StructT typfields; _}) -> 
    let pairs_without_names, dep_exp_typ_pairs = List.split (List.filter_map (fun b -> match b.it with 
      | ExpB (id', typ) -> Some ((VarE ("_" $ id'.at) $$ id'.at % typ, typ), (VarE id' $$ id'.at % typ, typ))
      | _ -> None
    ) binds) in
    let new_mixop = [] :: List.init (List.length dep_exp_typ_pairs + 1) (fun _ -> []) in
    let tupt = TupT (pairs_without_names @ [(VarE ("_" $ at) $$ at % user_typ, user_typ)]) $ at in
    let atoms = List.map (fun (a, _, _) -> a) typfields in
    let is_wrapped, pairs, rule_prems = split3concat (List.map (fun (_, (_, t, prems), _) ->
      let tups, wrapped = match t.it with 
        | TupT tups when List.exists (fun (e, _) -> non_empty_var e) tups -> tups, true
        | TupT [] -> [], false
        | _ -> [(VarE ("_" $ id.at) $$ id.at % t, t)], false
      in 
      ([wrapped], tups, prems)
    ) typfields) in

    let (rule_binds, pairs') = improve_ids_binders true at pairs in
    let new_prems = (List.filter_map get_exp_typ rule_binds |> List.concat_map (get_wf_pred env)) @ rule_prems in
    let str_exp = StrE (List.map2 (fun a ((e, t), wrapped) -> 
      let tupt = TupT [(e, t)] $ at in
      let tupe = TupE [e] $$ at % tupt in 
      if wrapped then (a, tupe) else 
      (a, e)
    ) atoms (List.combine pairs' is_wrapped)) $$ at % user_typ in 
    let tupe = TupE (List.map fst dep_exp_typ_pairs @ [str_exp]) $$ at % tupt in
    let rule = RuleD (id.it ^ "_" ^ rule_prefix $ id.at, List.map (transform_bind env) (binds @ rule_binds), new_mixop, tupe, List.map (transform_prem env) (new_prems)) $ at in
  
    if new_prems = [] then None else 
    let relation = RelD (wf_pred_prefix ^ id.it $ id.at, new_mixop, tupt, [rule]) $ at in 
    bind_wf_set env id.it;
    Some relation
  | _ -> None

let transform_rule env rule = 
  (match rule.it with
  | RuleD (id, binds, m, exp, prems) -> RuleD (id, 
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

let get_def_id def = 
  match def.it with 
  | TypD (id, _, _) -> id
  | _ -> "" $ def.at

let rec transform_def env def = 
  match def.it with
  | TypD (id, params, [inst]) when List.exists is_not_exp_param params -> 
    (TypD (id, List.map (transform_param env) params |> List.filter is_type_param, [inst]) $ def.at, [])
  | TypD (id, params, [inst]) -> 
    let relation = create_well_formed_predicate id env inst in
    (TypD (id, List.map (transform_param env) params |> List.filter is_type_param, [transform_inst env inst]) $ def.at, Option.to_list relation)
  | TypD (_, _, _) -> 
    error def.at "Multiples instances encountered, please run type family removal pass first."
  | RelD (id, m, typ, rules) -> 
    (RelD (id, m, transform_typ env typ, List.map (transform_rule env) rules) $ def.at, [])
  | DecD (id, params, typ, clauses) -> (DecD (id, List.map (transform_param env) params, transform_typ env typ, List.map (transform_clause env) clauses) $ def.at, [])
  | GramD (id, params, typ, prods) -> (GramD (id, List.map (transform_param env) params, transform_typ env typ, List.map (transform_prod env) prods) $ def.at, [])
  | RecD defs -> 
    if List.exists (needs_wfness env) defs 
      then List.iter (fun d -> bind_wf_set env (get_def_id d).it) defs; 

    let defs', wf_relations = List.map (transform_def env) defs |> List.split in
    let rec_defs = RecD defs' $ def.at in
    (rec_defs, [RecD (List.concat wf_relations) $ def.at])
  | HintD hintdef -> (HintD hintdef $ def.at, [])
  
let transform (il : script): script =
  let env = empty_env in 
  env.il_env <- Il.Env.env_of_script il;
  List.concat_map (fun d -> 
    let (t_d, wf_relations) = transform_def env d in 
    t_d :: wf_relations
  ) il