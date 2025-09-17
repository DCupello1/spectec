open Il.Ast
open Util.Source
open Util
open Il

let make_prefix = "mk_"
let name_prefix id = id.it ^ "_" 
let error at msg = Error.error at "MIL Preprocessing" msg

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

let check_type_family insts = 
  match insts with
  | [] -> false
  | [inst] when check_normal_type_creation inst -> false
  | _ -> true

let rec transform_iter env i =
  match i with 
  | ListN (exp, id_opt) -> ListN (transform_exp env exp, id_opt)
  | _ -> i

and transform_typ env t = 
  (match t.it with
  | VarT (id, args) -> 
    (* If it is a type family, try to reduce it to simplify the typing later on *)
    (match (Env.find_opt_typ env id) with
      | Some (_, insts) when check_type_family insts -> (Eval.reduce_typ env t).it
      | _ -> VarT (id, List.map (transform_arg env) args)
    )
  | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (transform_exp env e, transform_typ env t)) exp_typ_pairs)
  | IterT (typ, iter) -> IterT (transform_typ env typ, transform_iter env iter)
  | typ -> typ
  ) $ t.at

and transform_exp env e =  
  let typ = transform_typ env e.note in
  let t_func = transform_exp env in
  (match e.it with
  | VarE id -> VarE id
  | CaseE (m, e1) -> CaseE (m, t_func e1) 
  | CallE (fun_id, fun_args)-> CallE (fun_id, List.map (transform_arg env) fun_args) 
  | UnE (unop, optyp, e1) -> UnE (unop, optyp, t_func e1) 
  | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2) 
  | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2) 
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
  | IterE (e1, (iter, id_exp_pairs)) -> IterE (t_func e1, (transform_iter env iter, List.map (fun (id, exp) -> (id, t_func exp)) id_exp_pairs)) 
  | CvtE (e1, nt1, nt2) -> CvtE (t_func e1, nt1, nt2) 
  | SubE (e1, t1, t2) -> SubE (t_func e1, transform_typ env t1, transform_typ env t2) 
  | exp -> exp 
  ) $$ e.at % typ

and transform_path env p = 
  (match p.it with
  | RootP -> RootP
  | IdxP (p, e) -> IdxP (transform_path env p, transform_exp env e)
  | SliceP (p, e1, e2) -> SliceP (transform_path env p, transform_exp env e1, transform_exp env e2)
  | DotP (p, a) -> DotP (transform_path env p, a)
  ) $$ p.at % (transform_typ env p.note)

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
  | NegPr prem' -> NegPr (transform_prem env prem')
  | IfPr e -> IfPr (transform_exp env e)
  | LetPr (e1, e2, ids) -> LetPr (transform_exp env e1, transform_exp env e2, ids)
  | ElsePr -> ElsePr
  | IterPr (prem1, (iter, id_exp_pairs)) -> IterPr (transform_prem env prem1, 
      (transform_iter env iter, List.map (fun (id, exp) -> (id, transform_exp env exp)) id_exp_pairs)
    )
  ) $ prem.at

let transform_rule env rule = 
  match rule.it with
  | RuleD (id, binds, m, exp, prems) -> 
    RuleD (id, 
    List.map (transform_bind env) binds, 
    m, 
    transform_exp env exp, 
    List.map (transform_prem env) prems) $ rule.at

let transform_clause _id env clause =
  match clause.it with 
  | DefD (binds, args, exp, prems) -> 
    DefD ((List.map (transform_bind env) binds), 
    List.map (transform_arg env) args, 
    transform_exp env exp, 
    List.map (transform_prem env) prems) $ clause.at

let transform_prod env prod = 
  (match prod.it with 
  | ProdD (binds, sym, exp, prems) -> ProdD (List.map (transform_bind env) binds,
    transform_sym env sym,
    transform_exp env exp,
    List.map (transform_prem env) prems
  )
  ) $ prod.at

let transform_deftyp env deftyp = 
  (match deftyp.it with
  | AliasT typ -> AliasT (transform_typ env typ)
  | StructT typfields -> StructT (List.map (fun (a, (bs, t, prems), hints) -> 
    (a, (List.map (transform_bind env) bs, transform_typ env t, List.map (transform_prem env) prems), hints)) typfields)
  | VariantT typcases -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> 
    (m, (List.map (transform_bind env) bs, transform_typ env t, List.map (transform_prem env) prems), hints)) typcases)
  ) $ deftyp.at

let transform_inst env inst =
  match inst.it with 
  | (InstD (binds, args, deftyp)) -> 
    [InstD (List.map (transform_bind env) binds, List.map (transform_arg env) args, transform_deftyp env deftyp) $ inst.at]
 
  
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
  | RelD (id, m, typ, rules) -> RelD (id, m, transform_typ env typ, List.map (transform_rule env) rules)
  | DecD (id, params, typ, clauses) -> DecD (id, List.map (transform_param env) params, transform_typ env typ, List.map (transform_clause id env) clauses)
  | GramD (id, params, typ, prods) -> GramD (id, List.map (transform_param env) params, transform_typ env typ, List.map (transform_prod env) prods)
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