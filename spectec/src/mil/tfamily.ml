open Il.Ast
open Util.Source
open Il
open Xl

let type_family_prefix = "CASE_"

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

let check_type_family insts = 
  match insts with
    | [] -> false
    | [inst] when check_normal_type_creation inst -> false
    | _ -> true

let bind_to_string bind = 
  match bind.it with
    | ExpB (id, _) -> id.it
    | TypB id -> id.it
    | DefB (id, _, _) -> id.it
    | GramB (id, _, _) -> id.it

let is_var_typ t =
  match t.it with
    | VarT (_, _) -> true
    | _ -> false

let get_var_typ typ = 
  match typ.it with
    | VarT (id, args) -> (id, args)
    | _ -> assert false

let sub_type_name binds = (String.concat "_" (List.map bind_to_string binds))

let rec get_binds_from_inst env args = function
  | None -> None  (* id is a type parameter *)
  | Some (_ps, []) -> None
  | Some ([], _) -> None
  | Some (ps, {it = InstD (binds, args', _dt); _}::insts') ->
    match Eval.match_list Eval.match_arg env Subst.empty args args' with
    | exception Eval.Irred -> get_binds_from_inst env args (Some (ps, insts'))
    | None -> get_binds_from_inst env args (Some (ps, insts'))
    | Some _ -> Some binds

let rec transform_iter is_match env i =
  match i with 
    | ListN (exp, id_opt) -> ListN (transform_exp is_match env exp, id_opt)
    | _ -> i

and transform_typ is_match env t = 
  (match t.it with
    | VarT (id, args) -> 
      (* If it is a type family, try to reduce it to simplify the typing later on *)
      (match (Env.find_opt_typ env id) with
        | Some (_, insts) when check_type_family insts -> (Eval.reduce_typ env t).it
        | _ -> VarT (id, List.map (transform_arg is_match env) args)
      )
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (transform_exp is_match env e, transform_typ is_match env t)) exp_typ_pairs)
    | IterT (typ, iter) -> IterT (transform_typ is_match env typ, transform_iter is_match env iter)
    | typ -> typ
  ) $ t.at

(* TODO fix typing of new cases expressions *)
and transform_exp is_match env e =  
  let t_func = transform_exp is_match env in
  (match e.it with
    (* Specific type family handling for variable and case expressions*)
    | VarE _ when is_match && is_var_typ e.note ->
      let (id, args) = get_var_typ e.note in 
      let opt = Env.find_opt_typ env id in
      (match (get_binds_from_inst env args opt) with
        | None -> e.it
        | Some binds -> 
          let new_mixop = [[Atom.Atom (type_family_prefix ^ sub_type_name binds) $$ e.at % Atom.info ""]] in
          CaseE (new_mixop, e.it $$ e.at % Eval.reduce_typ env e.note )
      )
    | CaseE (m, e1) when is_match -> 
      let (id, args) = get_var_typ e.note in 
      let opt = Env.find_opt_typ env id in
      (match (get_binds_from_inst env args opt) with
        | None -> CaseE (m, t_func e1)
        | Some binds -> 
          let new_mixop = [[Atom.Atom (type_family_prefix ^ sub_type_name binds) $$ e.at % Atom.info ""]] in
          CaseE (new_mixop, CaseE (m, t_func e1) $$ e.at % Eval.reduce_typ env e.note)
      )
    (* Descend *)
    | UnE (unop, optyp, e1) -> UnE (unop, optyp, t_func e1)
    | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2)
    | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2)
    | TupE (exps) -> TupE (List.map t_func exps)
    | ProjE (e1, n) -> ProjE (t_func e1, n)
    | CaseE (m, e1) -> CaseE (m, t_func e1)
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
    | CallE (id, args) -> CallE (id, List.map (transform_arg is_match env) args)
    | IterE (e1, (iter, id_exp_pairs)) -> IterE (t_func e1, (transform_iter is_match env iter, List.map (fun (id, exp) -> (id, t_func exp)) id_exp_pairs))
    | CvtE (e1, nt1, nt2) -> CvtE (t_func e1, nt1, nt2)
    | SubE (e1, t1, t2) -> SubE (t_func e1, transform_typ is_match env t1, transform_typ is_match env t2)
    | exp -> exp
  ) $$ e.at % (transform_typ is_match env e.note)

and transform_path is_match env p = 
  (match p.it with
    | RootP -> RootP
    | IdxP (p, e) -> IdxP (transform_path is_match env p, transform_exp is_match env e)
    | SliceP (p, e1, e2) -> SliceP (transform_path is_match env p, transform_exp is_match env e1, transform_exp is_match env e2)
    | DotP (p, a) -> DotP (transform_path is_match env p, a)
  ) $$ p.at % (transform_typ is_match env p.note)

and transform_sym env s = 
  (match s.it with
    | VarG (id, args) -> VarG (id, List.map (transform_arg false env) args)
    | SeqG syms | AltG syms -> SeqG (List.map (transform_sym env) syms)
    | RangeG (syml, symu) -> RangeG (transform_sym env syml, transform_sym env symu)
    | IterG (sym, (iter, id_exp_pairs)) -> IterG (transform_sym env sym, (transform_iter false env iter, 
        List.map (fun (id, exp) -> (id, transform_exp false env exp)) id_exp_pairs)
      )
    | AttrG (e, sym) -> AttrG (transform_exp false env e, transform_sym env sym)
    | sym -> sym 
  ) $ s.at 

and transform_arg is_match env a =
  (match a.it with
    | ExpA exp -> ExpA (transform_exp is_match env exp)
    | TypA typ -> TypA (transform_typ is_match env typ)
    | DefA id -> DefA id
    | GramA sym -> GramA (transform_sym env sym)
  ) $ a.at

and transform_bind env b =
  (match b.it with
    | ExpB (id, typ) -> ExpB (id, transform_typ false env typ)
    | TypB id -> TypB id
    | DefB (id, params, typ) -> DefB (id, List.map (transform_param env) params, transform_typ false env typ)
    | GramB (id, params, typ) -> GramB (id, List.map (transform_param env) params, transform_typ false env typ)
  ) $ b.at 
  
and transform_param env p =
  (match p.it with
    | ExpP (id, typ) -> ExpP (id, transform_typ false env typ)
    | TypP id -> TypP id
    | DefP (id, params, typ) -> DefP (id, List.map (transform_param env) params, transform_typ false env typ)
    | GramP (id, typ) -> GramP (id, transform_typ false env typ)
  ) $ p.at 

let rec transform_prem env prem = 
  (match prem.it with
    | RulePr (id, m, e) -> RulePr (id, m, transform_exp false env e)
    | IfPr e -> IfPr (transform_exp false env e)
    | LetPr (e1, e2, ids) -> LetPr (transform_exp false env e1, transform_exp false env e2, ids)
    | ElsePr -> ElsePr
    | IterPr (prem1, (iter, id_exp_pairs)) -> IterPr (transform_prem env prem1, 
        (transform_iter false env iter, List.map (fun (id, exp) -> (id, transform_exp false env exp)) id_exp_pairs)
      )
  ) $ prem.at

let transform_rule env rule = 
  (match rule.it with
    | RuleD (id, binds, m, exp, prems) -> RuleD (id, 
      List.map (transform_bind env) binds, 
      m, 
      transform_exp false env exp, 
      List.map (transform_prem env) prems
    )
  ) $ rule.at

let transform_clause env clause =
  (match clause.it with 
    | DefD (binds, args, exp, prems) -> DefD (List.map (transform_bind env) binds, 
      List.map (transform_arg true env) args,
      transform_exp false env exp, 
      List.map (transform_prem env) prems
    )
  ) $ clause.at

let transform_prod env prod = 
  (match prod.it with 
    | ProdD (binds, sym, exp, prems) -> ProdD (List.map (transform_bind env) binds,
      transform_sym env sym,
      transform_exp false env exp,
      List.map (transform_prem env) prems
    )
  ) $ prod.at

let transform_deftyp env deftyp = 
  (match deftyp.it with
    | AliasT typ -> AliasT (transform_typ false env typ)
    | StructT typfields -> StructT (List.map (fun (a, (bs, t, prems), hints) -> (a, (List.map (transform_bind env) bs, transform_typ false env t, List.map (transform_prem env) prems), hints)) typfields)
    | VariantT typcases -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> (m, (List.map (transform_bind env) bs, transform_typ false env t, List.map (transform_prem env) prems), hints)) typcases)
  ) $ deftyp.at

let transform_inst env inst =
  (match inst.it with 
    | InstD (binds, args, deftyp) -> InstD (List.map (transform_bind env) binds, List.map (transform_arg false env) args, transform_deftyp env deftyp)
  ) $ inst.at

let rec transform_def env def = 
  (match def.it with
      | TypD (id, [], [inst]) -> TypD (id, [], [transform_inst env inst])
      | TypD (id, params, insts) -> TypD (id, List.map (transform_param env) params, List.map (transform_inst env) insts)
      | RecD defs -> RecD (List.map (transform_def env) defs)
      | RelD (id, m, typ, rules) -> RelD (id, m, transform_typ false env typ, List.map (transform_rule env) rules)
      | DecD (id, params, typ, clauses) -> DecD (id, List.map (transform_param env) params, transform_typ false env typ, List.map (transform_clause env) clauses)
      | GramD (id, params, typ, prods) -> GramD (id, List.map (transform_param env) params, transform_typ false env typ, List.map (transform_prod env) prods)
      | d -> d
  ) $ def.at
  
(* Creates new TypD's for each StructT and VariantT *)
let create_types id inst = 
  match inst.it with
    | InstD (binds, _, deftyp) -> (match deftyp.it with 
      | AliasT _ -> []
      | StructT _ | VariantT _ ->         
        let inst = InstD(binds, [], deftyp) $ inst.at in 
        [TypD (id.it ^ sub_type_name binds $ id.at, [], [inst])]
    )

let rec transform_type_family def =
  (match def.it with
    | TypD (id, _, [inst]) when check_normal_type_creation inst -> 
      (* Differenciate normal types from type families through the lack of params *)
      [TypD (id, [], [inst])]
    | TypD (id, params, insts) -> let types = List.concat_map (create_types id) insts in
      let transformed_instances = List.map (fun inst -> match inst.it with 
        | InstD (binds, args, {it = StructT _; at; _}) | InstD(binds, args, {it = VariantT _; at; _}) -> 
          InstD (binds, args, AliasT (VarT (id.it ^ sub_type_name binds $ id.at, List.map make_arg binds) $ id.at) $ at) $ inst.at
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