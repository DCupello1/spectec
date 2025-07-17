open Il.Ast
open Util.Source
open Il
open Util
open Il.Subst

(* Exception raised when a type has unbounded cases *)
exception UnboundedArg of string

module TypSet = Set.Make(struct
  type t = Il.Ast.typ
  let compare typ1 typ2 = if Eq.eq_typ typ1 typ2 then 0 
    (* HACK - Need better way to compare types, only hurts performance *)
    else String.compare (Print.string_of_typ typ1) (Print.string_of_typ typ2)
end)

module ExpSet = Set.Make(struct
  type t = Il.Ast.exp
  let compare exp1 exp2 = if Eq.eq_exp exp1 exp2 then 0
    (* HACK - Need better way to compare exps, only hurts performance *)
    else String.compare (Print.string_of_exp exp1) (Print.string_of_exp exp2)
end)

let type_family_prefix = "CASE_"
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

let empty_tuple_exp at = TupE [] $$ at % (TupT [] $ at)

let to_string_atom (a : atom) = 
  match a.it with
    | Atom s -> s
    | _ -> ""

let to_string_mixop (m : mixop) = 
  let is_atomid (a : atom) =
    match a.it with
      | Atom _ -> true
      | _ -> false
  in
  match m with
  | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> a
  | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map to_string_atom (List.filter is_atomid atoms))) mixop
    )

let rec to_string_exp (exp : exp) : string = 
  match exp.it with
    | BoolE _ | NumE _ | TextE _ -> Print.string_of_exp exp
    | ListE exps -> "l" ^ String.concat "_" (List.map to_string_exp exps) 
    | TupE [] -> ""
    | TupE exps -> String.concat "_" (List.map to_string_exp exps) 
    | CaseE (mixop, {it = TupE []; _}) -> to_string_mixop mixop 
    | CaseE (_mixop, exp) -> to_string_exp exp
    | OptE (Some e) -> "some_" ^ to_string_exp e
    | CvtE (e, _, _) -> to_string_exp e
    | SubE (e, _, _) -> to_string_exp e
    | _ -> assert false

let to_string_exps exps = 
  match exps with
    | [] -> ""
    | _ -> "_" ^ String.concat "_" (List.map to_string_exp exps)

let rec check_recursive_type (id : id) (t : typ): bool =
  match t.it with
    | VarT (typ_id, _) -> id = typ_id
    | IterT (typ, _iter) -> check_recursive_type id typ
    | TupT exp_typ_pairs -> List.exists (fun (_, typ) -> check_recursive_type id typ) exp_typ_pairs
    | _ -> false

(* Computes the cartesian product of a given list. *)
let product_of_lists (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> v :: existing) lst) acc) [[]] lists

let product_of_lists_append (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> existing @ [v]) lst) acc) [[]] lists

let check_matching env (call_args : arg list) (match_args : arg list) = 
  Option.is_some (try Il.Eval.match_list Il.Eval.match_arg env Il.Subst.empty call_args match_args with Il.Eval.Irred -> None)

let rec get_all_case_instances env (var_id : id) (concrete_args : arg list) (inst : inst): exp' list =
  match inst.it with
    | InstD (_, args, deftyp) -> 
      let subst = Option.value (try Il.Eval.match_list Il.Eval.match_arg env Il.Subst.empty concrete_args args with Il.Eval.Irred -> None) ~default:Il.Subst.empty in
      let new_deftyp = Il.Subst.subst_deftyp subst deftyp in
      match new_deftyp.it with
      | AliasT typ -> get_all_case_instances_from_typ env typ
      | StructT _typfields -> []
      | VariantT typcases when List.for_all (fun (_, (_, t, _), _) -> t.it = TupT []) typcases -> 
        List.map (fun (m, _, _) -> CaseE(m, empty_tuple_exp no_region)) typcases
      | VariantT typcases -> 
        List.iter (fun (_, (_, t, _), _) -> 
          if check_recursive_type var_id t then raise (UnboundedArg (Print.string_of_typ t)) else () 
        ) typcases;
        List.concat_map (fun (m, (_, t, _), _) -> 
          let case_instances = get_all_case_instances_from_typ env t in
          List.map (fun e -> CaseE(m, e $$ t.at % t)) case_instances
        ) typcases 

and get_all_case_instances_from_typ env (typ: typ): exp' list  = 
  let apply_phrase t e = e $$ t.at % t in 
  match typ.it with
    | BoolT -> [BoolE false; BoolE true]
    | VarT(var_id, dep_args) -> let (_, insts) = Il.Env.find_typ env var_id in 
      (match insts with
        | [] -> [] (* Should never happen *)
        | [inst] when check_normal_type_creation inst -> get_all_case_instances env var_id dep_args inst
        | _ -> match List.find_opt (fun inst -> match inst.it with | InstD (_, args, _) -> check_matching env dep_args args) insts with
          | None -> raise (UnboundedArg (Print.string_of_typ typ))
          | Some inst -> get_all_case_instances env var_id dep_args inst
      )
    | TupT exp_typ_pairs -> let instances_list = List.map (fun (_, t) -> List.map (apply_phrase t) (get_all_case_instances_from_typ env t)) exp_typ_pairs in
      List.map (fun exps -> TupE exps) (product_of_lists_append instances_list)
    | IterT (t, Opt) -> 
      let instances = get_all_case_instances_from_typ env t in
      OptE None :: List.map (fun e -> OptE (Some (apply_phrase t e))) instances
    (* | _ -> print_endline ("Encountered invalid type " ^ string_of_typ typ); [] *)
    | _ -> raise (UnboundedArg (Print.string_of_typ typ))

let sub_type_name_binds binds = (String.concat "_" (List.map bind_to_string binds))

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
    | IfPr e -> IfPr (transform_exp env e)
    | LetPr (e1, e2, ids) -> LetPr (transform_exp env e1, transform_exp env e2, ids)
    | ElsePr -> ElsePr
    | IterPr (prem1, (iter, id_exp_pairs)) -> IterPr (transform_prem env prem1, 
        (transform_iter env iter, List.map (fun (id, exp) -> (id, transform_exp env exp)) id_exp_pairs)
      )
  ) $ prem.at

let collect_sub_matches env: (id * exp) list list ref * (module Iter.Arg) =
  let module Arg = 
    struct
      include Iter.Skip 
      let acc = ref []
      let visited = ref ExpSet.empty
      let visit_exp (exp : exp) = 
        match exp.it with
          | SubE ({it = VarE var_id; _} as e, t1, _t2) when not (ExpSet.mem e !visited) ->
            visited := ExpSet.add e !visited; 
            let case_instances = (try get_all_case_instances_from_typ env t1 with
            | UnboundedArg msg -> 
              print_endline ("WARNING: " ^ msg);
              print_endline ("For type: " ^ Il.Print.string_of_typ t1);
              []
            ) in
            acc := List.map (fun e' -> (var_id, e' $$ t1.at % t1)) case_instances :: !acc
          | _ -> ()
    end
  in Arg.acc, (module Arg)

let collect_types_families env: TypSet.t ref * (module Iter.Arg) =
  let module Arg = 
    struct
      include Iter.Skip 
      let acc = ref TypSet.empty
      let visit_typ (typ : typ) = 
        match typ.it with
          | VarT (id, _) ->
            let opt = Env.find_opt_typ env id in 
            (match opt with 
              | Some (_, insts) when check_type_family insts ->
                acc := TypSet.add typ !acc
              | _ -> () 
            )
          | _ -> ()

      let visit_exp (exp : exp) = 
        match exp.it with
          | CaseE _ | CallE _ -> visit_typ exp.note 
          | _ -> ()
    end
  in Arg.acc, (module Arg)

let transform_rule env rule = 
  match rule.it with
    | RuleD (id, binds, m, exp, prems) -> 
      let acc_typfams, (module Arg: Iter.Arg) = collect_types_families env in
      let acc_cases, (module Arg': Iter.Arg) = collect_sub_matches env in
      let module TypAcc = Iter.Make(Arg) in
      let module SubAcc = Iter.Make(Arg') in
      TypAcc.binds binds;
      TypAcc.exp exp;
      TypAcc.prems prems;
      List.iter (SubAcc.typ) (TypSet.elements !acc_typfams);
      let cases_list = product_of_lists !acc_cases in
      let subst_list = List.map (List.fold_left (fun acc (id, exp) -> 
        Il.Subst.add_varid acc id exp) Il.Subst.empty
      ) cases_list in
      List.map (fun subst -> 
        let bindings = Il.Subst.Map.bindings subst.varid in
        let filtered_binds = List.filter (fun b -> 
          match b.it with
            | ExpB (id, _) -> not (mem_varid subst id)
            | _ -> true  
        ) binds in
        let (new_binds, _) = Il.Subst.subst_binds subst filtered_binds in
        let new_prems = Il.Subst.subst_list Il.Subst.subst_prem subst prems in
        let new_exp = Il.Subst.subst_exp subst exp in
        RuleD (id.it ^ to_string_exps (List.map snd bindings) $ id.at, 
        List.map (transform_bind env) new_binds, 
        m, 
        transform_exp env new_exp, 
        List.map (transform_prem env) new_prems) $ rule.at
      ) subst_list

let transform_clause _id env clause =
  match clause.it with 
    | DefD (binds, args, exp, prems) -> 
      let acc_cases, (module Arg: Iter.Arg) = collect_sub_matches env in
      let module Acc = Iter.Make(Arg) in
      Acc.args args;
      Acc.binds binds;
      Acc.exp exp;
      Acc.prems prems;
      let cases_list = product_of_lists !acc_cases in
      let subst_list = List.map (List.fold_left (fun acc (id, exp) -> 
        Il.Subst.add_varid acc id exp) Il.Subst.empty
      ) cases_list in
      List.map (fun subst -> 
        let (new_binds, _) = Il.Subst.subst_binds subst binds in
        let new_args = Il.Subst.subst_args subst args in
        let new_prems = Il.Subst.subst_list Il.Subst.subst_prem subst prems in
        let new_exp = Il.Subst.subst_exp subst exp in
        DefD ((List.map (transform_bind env) new_binds), 
        List.map (transform_arg env) new_args, 
        transform_exp env new_exp, 
        List.map (transform_prem env) new_prems) $ clause.at
      ) subst_list
  
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
    | StructT typfields -> StructT (List.map (fun (a, (bs, t, prems), hints) -> (a, (List.map (transform_bind env) bs, transform_typ env t, List.map (transform_prem env) prems), hints)) typfields)
    | VariantT typcases -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> (m, (List.map (transform_bind env) bs, transform_typ env t, List.map (transform_prem env) prems), hints)) typcases)
  ) $ deftyp.at

let transform_inst env inst =
  (match inst.it with 
    | (InstD (binds, args, deftyp)) when check_normal_type_creation inst -> 
      [InstD (List.map (transform_bind env) binds, List.map (transform_arg env) args, transform_deftyp env deftyp) $ inst.at]
    | InstD (binds, args, deftyp) -> 
      let acc_cases, (module Arg: Iter.Arg) = collect_sub_matches env in
      let module Acc = Iter.Make(Arg) in
      Acc.args args;
      let cases_list = product_of_lists !acc_cases in
      let subst_list = List.map (List.fold_left (fun acc (id, exp) -> 
        Il.Subst.add_varid acc id exp) Il.Subst.empty
      ) cases_list in
      List.map (fun subst -> 
        let (new_binds, _) = Il.Subst.subst_binds subst binds in
        let new_args = Il.Subst.subst_args subst args in
        let new_deftyp = Il.Subst.subst_deftyp subst deftyp in
        InstD (List.map (transform_bind env) new_binds, List.map (transform_arg env) new_args, transform_deftyp env new_deftyp) $ inst.at
      ) subst_list
  )

let remove_overlapping_cases env insts = 
  Lib.List.nub (fun inst inst' -> match inst.it, inst'.it with
    | InstD (_, args, _), InstD (_, args', _) -> 
      (* Reduction is done here to remove subtyping expressions *)
      let reduced_args = List.map (Eval.reduce_arg env) args in
      let reduced_args' = List.map (Eval.reduce_arg env) args' in
      Eq.eq_list Eq.eq_arg reduced_args reduced_args'
  ) insts

let rec transform_def env def = 
  (match def.it with
    | TypD (id, params, [inst]) when check_normal_type_creation inst -> TypD (id, params, transform_inst env inst)
    | TypD (id, params, insts) -> 
      let new_insts = List.concat_map (transform_inst env) insts in
      TypD (id, List.map (transform_param env) params, remove_overlapping_cases env new_insts)
    | RecD defs -> RecD (List.map (transform_def env) defs)
    | RelD (id, m, typ, rules) -> RelD (id, m, transform_typ env typ, List.concat_map (transform_rule env) rules)
    | DecD (id, params, typ, clauses) -> DecD (id, List.map (transform_param env) params, transform_typ env typ, List.concat_map (transform_clause id env) clauses)
    | GramD (id, params, typ, prods) -> GramD (id, List.map (transform_param env) params, transform_typ env typ, List.map (transform_prod env) prods)
    | d -> d
  ) $ def.at
  
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
    | InstD (binds, _, deftyp) -> (match deftyp.it with 
      | AliasT _ -> []
      | StructT _ | VariantT _ ->         
        let inst = InstD(binds, List.map make_arg binds, deftyp) $ inst.at in 
        [TypD (id.it ^ sub_type_name_binds binds $ id.at, List.map make_param_from_bind binds, [inst])]
    )

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