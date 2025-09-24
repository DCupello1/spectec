open Il.Ast
open Util.Source
open Util
open Il

let make_prefix = "mk_"
let name_prefix id = id.it ^ "_" 
let proj_prefix = "proj_"
let error at msg = Error.error at "MIL Preprocessing" msg

module StringMap = Map.Make(String)
type bind_map = typ StringMap.t

let get_tuple_exp e =
  match e.it with
    | TupE exps -> exps
    | _ -> [e]

let get_tuple_typ t =
  match t.it with
    | TupT typs -> List.map snd typs
    | _ -> [t]

let make_arg b = 
  (match b.it with
  | ExpB (id, typ) -> ExpA (VarE id $$ id.at % typ) 
  | TypB id -> TypA (VarT (id, []) $ id.at) (* TODO unsure this makes sense*)
  | DefB (id, _, _) -> DefA id 
  | GramB (_, _, _) -> assert false (* Avoid this *)
  ) $ b.at

(* HACK This is used to distinguish between normal types and type families *)
let check_normal_type_creation (inst : inst) : bool = 
  match inst.it with
  | InstD (_, args, _) -> List.for_all (fun arg -> 
    match arg.it with 
    (* Args in normal types can really only be variable expressions or type params *)
    | ExpA {it = VarE _; _} | TypA _ -> true
    | _ -> false  
    ) args 

let bind_to_string bind = 
  match bind.it with
  | ExpB (id, _) -> id.it
  | TypB id -> id.it
  | DefB (id, _, _) -> id.it
  | GramB (id, _, _) -> id.it

let sub_type_name_binds binds = (String.concat "_" (List.map bind_to_string binds))
let constructor_name' id binds = make_prefix ^ name_prefix id ^ sub_type_name_binds binds
let constructor_name id binds = constructor_name' id binds $ id.at 
let proj_name id binds = proj_prefix ^ name_prefix id ^ sub_type_name_binds binds $ id.at

let check_type_family insts = 
  match insts with
  | [] -> false
  | [inst] when check_normal_type_creation inst -> false
  | _ -> true

let make_bind_set binds = 
  List.fold_left (fun acc b -> 
    match b.it with 
    | ExpB (id, typ) -> StringMap.add id.it typ acc
    | _ -> acc  
  ) StringMap.empty binds

let rec get_real_typ_from_exp bind_map env e =  
  match e.it with
  | VarE id -> (match StringMap.find_opt id.it bind_map with
    | Some typ -> typ 
    | None -> e.note
  )
  (* TODO - only assumes functions, not function params *)
  | CallE (id, _) -> (match (Env.find_opt_def env id) with
    | Some (_, typ, _) -> 
      print_endline ("hallo: " ^ (Print.string_of_typ typ));
      typ
    | None -> e.note
  )
  | NumE (`Nat _) -> NumT `NatT $ e.at
  | NumE (`Int _) -> NumT `IntT $ e.at
  | NumE (`Rat _) -> NumT `RatT $ e.at
  | NumE (`Real _) -> NumT `RealT $ e.at
  | BoolE _ -> BoolT $ e.at
  | TextE _ -> TextT $ e.at
  | TupE es -> let typs = List.map (get_real_typ_from_exp bind_map env) es in
    TupT (List.map (fun t -> (VarE ("_" $ t.at) $$ t.at % t, t)) typs) $ e.at
  | ListE (e' :: _) -> 
    let iter = (match e.note.it with 
      | IterT (_, i) -> i
      | _ -> List
    ) in
    let t = get_real_typ_from_exp bind_map env e' in
    IterT (t, iter) $ e.at
  | OptE (Some e) -> let t = get_real_typ_from_exp bind_map env e in
    IterT (t, Opt) $ e.at
  | _ -> e.note

and get_real_typ_from_arg bind_map env arg =
  match arg.it with
    | ExpA exp -> Some (get_real_typ_from_exp bind_map env exp)
    | TypA typ -> Some typ
    | _ -> None

let rec is_family_typ env typ = 
  match typ.it with
    | VarT (id, _) -> 
      (match (Env.find_opt_typ env id) with
        | Some (_, insts) when check_type_family insts -> true
        | _ -> false
    )
    | IterT (t, _) -> is_family_typ env t
    | _ -> false
      
let get_family_type_id env typ = 
  match typ.it with
    | VarT (id, _) -> 
      (match (Env.find_opt_typ env id) with
        | Some (_, insts) when check_type_family insts -> Some id
        | _ -> None
    )
    | _ -> None

let check_type_equality env typ expected_typ = 
  let r_typ = Eval.reduce_typ env typ in
  let r_expected_typ = Eval.reduce_typ env expected_typ in
  Eq.eq_typ r_typ r_expected_typ

let rec get_binds_from_inst env expected_typ = function
  | [] -> None
  | {it = InstD (binds, _, {it = AliasT typ; _}); _}::insts' ->
    if check_type_equality env typ expected_typ then Some binds else 
    (match (Eval.match_typ env Subst.empty typ expected_typ) with 
      | exception Eval.Irred -> get_binds_from_inst env expected_typ insts'
      | Some _subst -> Some binds
      | _ -> get_binds_from_inst env expected_typ insts'
    )
  | _ -> None

let get_family_type_binds env family_typ expected_typ = 
  match family_typ.it with
    | VarT (id, _) -> 
      (* If it is a type family, try to reduce it to simplify the typing later on *)
      (match (Env.find_opt_typ env id) with
        | Some (_, insts) when check_type_family insts -> 
          Option.map (fun binds -> (id, binds)) (get_binds_from_inst env expected_typ insts)
        | _ -> None
    )
    | _ -> None

let apply_conversion env exp expected_typ real_typ = 
  match (is_family_typ env real_typ, is_family_typ env expected_typ) with
    | true, false ->
      (* We know that the real type is a type family, so its expected type must be one of its sub types. Look it up *)
      let reduced_typ = Eval.reduce_typ env expected_typ in
      let binds_opt = get_family_type_binds env real_typ expected_typ in
      (match binds_opt with 
      | Some (id, binds) -> 
        let proj_exp = CallE (proj_name id binds, [ExpA ({exp with note = real_typ}) $ exp.at]) $$ exp.at % reduced_typ in
        proj_exp
      | None -> exp
      )
    | false, true -> 
      (* Since we know the real type is not a family type, then we need to upcast it *)
      SubE({exp with note = real_typ}, real_typ, expected_typ) $$ exp.at % expected_typ
    | _ -> 
      (* Conservative - we don't change anything *)
      exp

let apply_conversion_call_arg bind_map env p a = 
  match p.it, a.it with
  | ExpP (_, expected_typ), ExpA e -> 
    let real_typ = get_real_typ_from_exp bind_map env e in 
    let matched = Eq.eq_typ real_typ expected_typ in
    if matched then a else 
    ExpA (apply_conversion env e expected_typ real_typ) $ a.at
  | _ -> a

let apply_conversion_case_exp bind_map env typ m e =
  let exps = get_tuple_exp e in 
  let reduced_typ_id = Print.string_of_typ_name (Eval.reduce_typ env typ) $ no_region in 
  match (Env.find_opt_typ env reduced_typ_id) with
  | Some (_, [({it = InstD (_, _, {it = VariantT typcases; _}); _} as inst)]) when check_normal_type_creation inst -> 
    let f = List.find_map (fun (m', (_, t, _), _) -> 
      let typs = get_tuple_typ t in 
      if Eq.eq_mixop m m' then Some typs else None
    ) typcases in 
    (match f with
    | Some typs ->
      let new_exps = List.map2 (fun e' expected_typ -> 
        let real_typ = get_real_typ_from_exp bind_map env e' in
        let matched = Eq.eq_typ real_typ expected_typ in
        if matched then e' else 
        apply_conversion env e' expected_typ real_typ
      ) exps typs in
      TupE new_exps $$ e.at % e.note
    | _ -> e
    )
  | _ -> e

let rec transform_iter bind_map env i =
  match i with 
  | ListN (exp, id_opt) -> ListN (transform_exp bind_map env exp, id_opt)
  | _ -> i

and transform_typ bind_map env t = 
  (match t.it with
  | VarT (id, args) -> VarT (id, List.map (transform_arg bind_map env) args)
  | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (transform_exp bind_map env e, transform_typ bind_map env t)) exp_typ_pairs)
  | IterT (typ, iter) -> IterT (transform_typ bind_map env typ, transform_iter bind_map env iter)
  | typ -> typ
  ) $ t.at

and transform_exp bind_map env e =  
  let typ = transform_typ bind_map env e.note in
  let t_func = transform_exp bind_map env in
  (match e.it with
  | VarE id -> VarE id
  | CaseE (m, e1) -> 
    let new_args = apply_conversion_case_exp bind_map env e.note m (t_func e1) in
    (match (get_family_type_id env e.note) with 
    | Some _ -> SubE (CaseE (m, new_args) $$ e.at % typ, typ, e.note)  
    | _ -> CaseE (m, new_args)  
    )
  | CallE (fun_id, fun_args) -> 
    (match (Env.find_opt_def env fun_id) with
    | Some (params, _, _) -> 
      let fun_args' = List.map (transform_arg bind_map env) fun_args in
      let new_args = List.map2 (fun a p -> apply_conversion_call_arg bind_map env p a) fun_args' params in
      CallE (fun_id, new_args)
    | None -> CallE (fun_id, List.map (transform_arg bind_map env) fun_args)
    )
  | UnE (unop, optyp, e1) -> UnE (unop, optyp, t_func e1) 
  | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2) 
  | CmpE (cmpop, optyp, e1, e2) -> 
    let t_e1 = t_func e1 in 
    let t_e2 = t_func e2 in
    let rel_typ1 = get_real_typ_from_exp bind_map env e1 in 
    let rel_typ2 = get_real_typ_from_exp bind_map env e2 in
    let expected_typ1 = transform_typ bind_map env t_e1.note in
    let expected_typ2 = transform_typ bind_map env t_e2.note in
    (match (Eq.eq_typ rel_typ1 expected_typ1, Eq.eq_typ rel_typ2 expected_typ2) with
    | false, true ->
      CmpE (cmpop, optyp, apply_conversion env t_e1 expected_typ1 rel_typ1, t_e2)
    | true, false -> 
      CmpE (cmpop, optyp, t_e1, apply_conversion env t_e2 expected_typ2 rel_typ2)
    | _ -> 
      CmpE (cmpop, optyp, t_e1, t_e2) 
    )
  | TupE (exps) -> TupE (List.map t_func exps) 
  | ProjE (e1, n) -> ProjE (t_func e1, n) 
  | UncaseE (e1, m) -> UncaseE (t_func e1, m) 
  | OptE e1 -> OptE (Option.map t_func e1) 
  | TheE e1 -> TheE (t_func e1) 
  | StrE fields -> StrE (List.map (fun (a, e1) -> (a, t_func e1)) fields) 
  | DotE (e1, a) -> DotE (t_func e1, a) 
  | CompE (e1, e2) -> CompE (t_func e1, t_func e2) 
  | ListE entries -> ListE (List.map t_func entries) 
  | LiftE e1 -> LiftE (t_func e1) 
  | MemE (e1, e2) -> MemE (t_func e1, t_func e2) 
  | LenE e1 -> LenE e1 
  | CatE (e1, e2) -> CatE (t_func e1, t_func e2) 
  | IdxE (e1, e2) -> IdxE (t_func e1, t_func e2) 
  | SliceE (e1, e2, e3) -> SliceE (t_func e1, t_func e2, t_func e3) 
  | UpdE (e1, p, e2) -> UpdE (t_func e1, p, t_func e2) 
  | ExtE (e1, p, e2) -> ExtE (t_func e1, p, t_func e2) 
  | IterE (e1, (iter, id_exp_pairs)) -> IterE (t_func e1, (transform_iter bind_map env iter, List.map (fun (id, exp) -> (id, t_func exp)) id_exp_pairs)) 
  | CvtE (e1, nt1, nt2) -> CvtE (t_func e1, nt1, nt2) 
  | SubE (e1, t1, t2) -> SubE (t_func e1, transform_typ bind_map env t1, transform_typ bind_map env t2) 
  | exp -> exp 
  ) $$ e.at % typ

and transform_path bind_map env p = 
  (match p.it with
  | RootP -> RootP
  | IdxP (p, e) -> IdxP (transform_path bind_map env p, transform_exp bind_map env e)
  | SliceP (p, e1, e2) -> SliceP (transform_path bind_map env p, transform_exp bind_map env e1, transform_exp bind_map env e2)
  | DotP (p, a) -> DotP (transform_path bind_map env p, a)
  ) $$ p.at % (transform_typ bind_map env p.note)

and transform_sym bind_map env s = 
  (match s.it with
  | VarG (id, args) -> VarG (id, List.map (transform_arg bind_map env) args)
  | SeqG syms | AltG syms -> SeqG (List.map (transform_sym bind_map env) syms)
  | RangeG (syml, symu) -> RangeG (transform_sym bind_map env syml, transform_sym bind_map env symu)
  | IterG (sym, (iter, id_exp_pairs)) -> IterG (transform_sym bind_map env sym, (transform_iter bind_map env iter, 
      List.map (fun (id, exp) -> (id, transform_exp bind_map env exp)) id_exp_pairs)
    )
  | AttrG (e, sym) -> AttrG (transform_exp bind_map env e, transform_sym bind_map env sym)
  | sym -> sym 
  ) $ s.at 

and transform_arg bind_map env a =
  (match a.it with
  | ExpA exp -> ExpA (transform_exp bind_map env exp)
  | TypA typ -> TypA (transform_typ bind_map env typ)
  | DefA id -> DefA id
  | GramA sym -> GramA (transform_sym bind_map env sym)
  ) $ a.at

and transform_bind env b =
  (match b.it with
  | ExpB (id, typ) -> ExpB (id, transform_typ StringMap.empty env typ)
  | TypB id -> TypB id
  | DefB (id, params, typ) -> DefB (id, List.map (transform_param env) params, transform_typ StringMap.empty env typ)
  | GramB (id, params, typ) -> GramB (id, List.map (transform_param env) params, transform_typ StringMap.empty env typ)
  ) $ b.at 
  
and transform_param env p =
  (match p.it with
  | ExpP (id, typ) -> ExpP (id, transform_typ StringMap.empty env typ)
  | TypP id -> TypP id
  | DefP (id, params, typ) -> DefP (id, List.map (transform_param env) params, transform_typ StringMap.empty env typ)
  | GramP (id, typ) -> GramP (id, transform_typ StringMap.empty env typ)
  ) $ p.at 

let rec transform_prem bind_map env prem = 
  (match prem.it with
  | RulePr (id, m, e) -> RulePr (id, m, transform_exp bind_map env e)
  | NegPr prem' -> NegPr (transform_prem bind_map env prem')
  | IfPr e -> IfPr (transform_exp bind_map env e)
  | LetPr (e1, e2, ids) -> LetPr (transform_exp bind_map env e1, transform_exp bind_map env e2, ids)
  | ElsePr -> ElsePr
  | IterPr (prem1, (iter, id_exp_pairs)) -> IterPr (transform_prem bind_map env prem1, 
      (transform_iter bind_map env iter, List.map (fun (id, exp) -> (id, transform_exp bind_map env exp)) id_exp_pairs)
    )
  ) $ prem.at

let transform_rule env rule = 
  match rule.it with
  | RuleD (id, binds, m, exp, prems) -> 
    let bind_map = make_bind_set binds in 
    RuleD (id, 
    List.map (transform_bind env) binds, 
    m, 
    transform_exp bind_map env exp, 
    List.map (transform_prem bind_map env) prems) $ rule.at

let transform_clause _id env clause =
  match clause.it with 
  | DefD (binds, args, exp, prems) -> 
    let bind_map = make_bind_set binds in 
    DefD ((List.map (transform_bind env) binds), 
    List.map (transform_arg bind_map env) args, 
    transform_exp bind_map env exp, 
    List.map (transform_prem bind_map env) prems) $ clause.at

let transform_prod env prod = 
  (match prod.it with 
  | ProdD (binds, sym, exp, prems) -> 
    let bind_map = make_bind_set binds in
    ProdD (List.map (transform_bind env) binds,
    transform_sym bind_map env sym,
    transform_exp bind_map env exp,
    List.map (transform_prem bind_map env) prems
  )
  ) $ prod.at

let transform_deftyp env deftyp = 
  (match deftyp.it with
  | AliasT typ -> AliasT (transform_typ StringMap.empty env typ)
  | StructT typfields -> StructT (List.map (fun (a, (bs, t, prems), hints) -> 
    let bind_map = make_bind_set bs in
    (a, (List.map (transform_bind env) bs, transform_typ bind_map env t, List.map (transform_prem bind_map env) prems), hints)) typfields)
  | VariantT typcases -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> 
    let bind_map = make_bind_set bs in
    (m, (List.map (transform_bind env) bs, transform_typ bind_map env t, List.map (transform_prem bind_map env) prems), hints)) typcases)
  ) $ deftyp.at

let transform_inst env inst =
  match inst.it with 
  | (InstD (binds, args, deftyp)) -> 
    [InstD (List.map (transform_bind env) binds, List.map (transform_arg StringMap.empty env) args, transform_deftyp env deftyp) $ inst.at]
 
  
(* Creates new TypD's for each StructT and VariantT *)
let create_types id inst = 
  let make_param_from_bind b = 
  (match b.it with 
  | ExpB (id, typ) -> ExpP (id, typ)
  | TypB id -> TypP id
  | DefB (id, params, typ) -> DefP (id, params, typ)
  | GramB _ -> assert false (* Avoid this *)
  ) $ b.at in
  match inst.it with
  | InstD (binds, _, deftyp) -> 
    (match deftyp.it with 
    | AliasT _ -> []
    | StructT _ | VariantT _ ->
      let inst = InstD(binds, List.map make_arg binds, deftyp) $ inst.at in 
      [TypD (id.it ^ sub_type_name_binds binds $ id.at, List.map make_param_from_bind binds, [inst])]
    )

let rec transform_def env def = 
  (match def.it with
  | TypD (id, params, insts) -> 
    let new_insts = List.concat_map (transform_inst env) insts in
    TypD (id, List.map (transform_param env) params, new_insts)
  | RecD defs -> RecD (List.map (transform_def env) defs)
  | RelD (id, m, typ, rules) ->
    print_endline "Testing...";
    print_endline (id.it);
    RelD (id, m, transform_typ StringMap.empty env typ, List.map (transform_rule env) rules)
  | DecD (id, params, typ, clauses) -> DecD (id, List.map (transform_param env) params, transform_typ StringMap.empty env typ, List.map (transform_clause id env) clauses)
  | GramD (id, params, typ, prods) -> GramD (id, List.map (transform_param env) params, transform_typ StringMap.empty env typ, List.map (transform_prod env) prods)
    | d -> d
  ) $ def.at

let rec transform_type_family def =
  (match def.it with
  | TypD (id, params, [inst]) when check_normal_type_creation inst -> [TypD (id, params, [inst])]
  | TypD (id, params, insts) -> let types = List.concat_map (create_types id) insts in
    let transformed_instances = List.map (fun inst -> match inst.it with 
      | InstD (binds, args, {it = StructT _; at; _}) | InstD(binds, args, {it = VariantT _; at; _}) -> 
        InstD (binds, args, AliasT (VarT (id.it ^ sub_type_name_binds binds $ id.at, List.map make_arg binds) $ id.at) $ at) $ inst.at
      | _ -> inst 
    ) insts in
    types @ [TypD(id, params, transformed_instances)]
  | RecD defs -> [RecD (List.concat_map transform_type_family defs)]
  | d -> [d]
  ) |> List.map (fun d -> d $ def.at)

let transform (il : script): script = 
  let il_transformed = List.concat_map transform_type_family il in
  let env = Env.env_of_script il_transformed in 
  List.map (transform_def env) il_transformed