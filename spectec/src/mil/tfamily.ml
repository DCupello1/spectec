open Il.Ast
open Util.Source
open Il
open Util

(* Exception raised when a type has unbounded cases *)
exception UnboundedArg of string

type exp_type =
  | MATCH
  | NORMAL
  | RETURN

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


let sub_type_name binds = (String.concat "_" (List.map bind_to_string binds))

let rec get_binded_exps e = 
  match e.it with
    | VarE _
    | CaseE (_, {it = TupE []; _}) -> [e]
    | CaseE (_, e) -> get_binded_exps e
    | TupE exps -> List.concat_map get_binded_exps exps
    | SubE (e, _, _) -> get_binded_exps e
    | CallE (_, args) -> List.concat_map get_binded_args args
    | _ -> 
      (* TODO - maybe extend this to other exps? *)
      error e.at ("This exp is not allowed in matching: " ^ Il.Print.string_of_exp e) 

and get_binded_args a = 
  match a.it with
    | ExpA e -> get_binded_exps e
    | _ -> error a.at "Type family Args are not allowed to have anything other than exp" 
    (* TODO remove this assumption later*)

let rec get_binds_from_inst env args = function
  | None -> None  (* id is a type parameter *)
  | Some (_ps, []) -> None
  | Some ([], _) -> None
  | Some (_, [inst]) when check_normal_type_creation inst -> None  
  | Some (ps, {it = InstD (binds, args', _dt); _} :: insts') ->
    match Eval.match_list Eval.match_arg env Subst.empty args args' with
    | exception Eval.Irred -> get_binds_from_inst env args (Some (ps, insts'))
    | None -> get_binds_from_inst env args (Some (ps, insts'))
    | Some _s -> 
      let exps = List.concat_map get_binded_args (List.map (Il.Eval.reduce_arg env) args) in
      assert (List.length binds == List.length exps);
      (* TODO - need to check that binds and exps are in the same order *)
      Some (exps, binds)

let rec transform_iter exp_type env i =
  match i with 
    | ListN (exp, id_opt) -> ListN (transform_exp exp_type env exp, id_opt)
    | _ -> i

and transform_typ exp_type env t = 
  (match t.it with
    | VarT (id, args) -> 
      (* If it is a type family, try to reduce it to simplify the typing later on *)
      (match (Env.find_opt_typ env id) with
        | Some (_, insts) when check_type_family insts -> (Eval.reduce_typ env t).it
        | _ -> VarT (id, List.map (transform_arg exp_type env) args)
      )
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (transform_exp exp_type env e, transform_typ exp_type env t)) exp_typ_pairs)
    | IterT (typ, iter) -> IterT (transform_typ exp_type env typ, transform_iter exp_type env iter)
    | typ -> typ
  ) $ t.at

(* TODO Come up with a better solution other than this handling *)
and transform_exp exp_type env e =  
  let typ = transform_typ exp_type env e.note in
  let t_func = transform_exp exp_type env in
  (match e.it with
    (* Specific type family handling for variable and case expressions *)
    | CaseE (m, e1) -> CaseE (m, t_func e1) $$ e.at % typ
    | CallE (fun_id, fun_args)-> 
      CallE (fun_id, List.map (transform_arg exp_type env) fun_args) $$ e.at % typ
    (* Descend *)
    | UnE (unop, optyp, e1) -> UnE (unop, optyp, t_func e1) $$ e.at % typ
    | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2) $$ e.at % typ
    | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2) $$ e.at % typ
    | TupE (exps) -> TupE (List.map t_func exps) $$ e.at % typ
    | ProjE (e1, n) -> ProjE (t_func e1, n) $$ e.at % typ
    | UncaseE (e1, m) -> UncaseE (t_func e1, m) $$ e.at % typ
    | OptE e1 -> OptE (Option.map t_func e1) $$ e.at % typ
    | TheE e1 -> TheE (t_func e1) $$ e.at % typ
    | StrE fields -> StrE (List.map (fun (a, e1) -> (a, t_func e1)) fields) $$ e.at % typ
    | DotE (e1, a) -> DotE (t_func e1, a) $$ e.at % typ
    | CompE (e1, e2) -> CompE (t_func e1, t_func e2) $$ e.at % typ
    | ListE entries -> ListE (List.map t_func entries) $$ e.at % typ
    | LiftE e1 -> LiftE (t_func e1) $$ e.at % typ
    | MemE (e1, e2) -> MemE (t_func e1, t_func e2) $$ e.at % typ
    | LenE e1 -> LenE e1 $$ e.at % typ
    | CatE (e1, e2) -> CatE (t_func e1, t_func e2) $$ e.at % typ
    | IdxE (e1, e2) -> IdxE (t_func e1, t_func e2) $$ e.at % typ
    | SliceE (e1, e2, e3) -> SliceE (t_func e1, t_func e2, t_func e3) $$ e.at % typ
    | UpdE (e1, p, e2) -> UpdE (t_func e1, p, t_func e2) $$ e.at % typ
    | ExtE (e1, p, e2) -> ExtE (t_func e1, p, t_func e2) $$ e.at % typ
    | IterE (e1, (iter, id_exp_pairs)) -> IterE (t_func e1, (transform_iter exp_type env iter, List.map (fun (id, exp) -> (id, t_func exp)) id_exp_pairs)) $$ e.at % typ
    | CvtE (e1, nt1, nt2) -> CvtE (t_func e1, nt1, nt2) $$ e.at % typ
    | SubE (e1, _, t2) when exp_type = MATCH || exp_type = RETURN -> (t_func e1).it $$ e.at % t2
    | SubE (e1, t1, t2) -> SubE (t_func e1, transform_typ exp_type env t1, transform_typ exp_type env t2) $$ e.at % typ
    | exp -> exp $$ e.at % typ
  ) 

and transform_path exp_type env p = 
  (match p.it with
    | RootP -> RootP
    | IdxP (p, e) -> IdxP (transform_path exp_type env p, transform_exp exp_type env e)
    | SliceP (p, e1, e2) -> SliceP (transform_path exp_type env p, transform_exp exp_type env e1, transform_exp exp_type env e2)
    | DotP (p, a) -> DotP (transform_path exp_type env p, a)
  ) $$ p.at % (transform_typ exp_type env p.note)

and transform_sym env s = 
  (match s.it with
    | VarG (id, args) -> VarG (id, List.map (transform_arg NORMAL env) args)
    | SeqG syms | AltG syms -> SeqG (List.map (transform_sym env) syms)
    | RangeG (syml, symu) -> RangeG (transform_sym env syml, transform_sym env symu)
    | IterG (sym, (iter, id_exp_pairs)) -> IterG (transform_sym env sym, (transform_iter NORMAL env iter, 
        List.map (fun (id, exp) -> (id, transform_exp NORMAL env exp)) id_exp_pairs)
      )
    | AttrG (e, sym) -> AttrG (transform_exp NORMAL env e, transform_sym env sym)
    | sym -> sym 
  ) $ s.at 

and transform_arg exp_type env a =
  (match a.it with
    | ExpA exp -> ExpA (transform_exp exp_type env exp)
    | TypA typ -> TypA (transform_typ exp_type env typ)
    | DefA id -> DefA id
    | GramA sym -> GramA (transform_sym env sym)
  ) $ a.at

and transform_bind env b =
  (match b.it with
    | ExpB (id, typ) -> ExpB (id, transform_typ NORMAL env typ)
    | TypB id -> TypB id
    | DefB (id, params, typ) -> DefB (id, List.map (transform_param env) params, transform_typ NORMAL env typ)
    | GramB (id, params, typ) -> GramB (id, List.map (transform_param env) params, transform_typ NORMAL env typ)
  ) $ b.at 
  
and transform_param env p =
  (match p.it with
    | ExpP (id, typ) -> ExpP (id, transform_typ NORMAL env typ)
    | TypP id -> TypP id
    | DefP (id, params, typ) -> DefP (id, List.map (transform_param env) params, transform_typ NORMAL env typ)
    | GramP (id, typ) -> GramP (id, transform_typ NORMAL env typ)
  ) $ p.at 

let rec transform_prem env prem = 
  (match prem.it with
    | RulePr (id, m, e) -> RulePr (id, m, transform_exp NORMAL env e)
    | IfPr e -> IfPr (transform_exp NORMAL env e)
    | LetPr (e1, e2, ids) -> LetPr (transform_exp NORMAL env e1, transform_exp NORMAL env e2, ids)
    | ElsePr -> ElsePr
    | IterPr (prem1, (iter, id_exp_pairs)) -> IterPr (transform_prem env prem1, 
        (transform_iter NORMAL env iter, List.map (fun (id, exp) -> (id, transform_exp NORMAL env exp)) id_exp_pairs)
      )
  ) $ prem.at

let transform_rule env rule = 
  (match rule.it with
    | RuleD (id, binds, m, exp, prems) -> RuleD (id, 
      List.map (transform_bind env) binds, 
      m, 
      transform_exp NORMAL env exp, 
      List.map (transform_prem env) prems
    )
  ) $ rule.at

let collect_sub_matches env: (id * exp) list list ref * (module Iter.Arg) =
  let module Arg = 
    struct
      include Iter.Skip 
      let acc = ref []
      let visit_exp (exp : exp) = 
        match exp.it with
          | SubE ({it = VarE var_id; _}, t1, _t2) -> 
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

let transform_clause _id env clause =
  match clause.it with 
    | DefD (binds, args, exp, prems) -> 
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
        let new_prems = Il.Subst.subst_list Il.Subst.subst_prem subst prems in
        let new_exp = Il.Subst.subst_exp subst exp in
        DefD ((List.map (transform_bind env) new_binds), 
        List.map (transform_arg MATCH env) new_args, 
        transform_exp RETURN env new_exp, 
        List.map (transform_prem env) new_prems) $ clause.at
      ) subst_list
  
let transform_prod env prod = 
  (match prod.it with 
    | ProdD (binds, sym, exp, prems) -> ProdD (List.map (transform_bind env) binds,
      transform_sym env sym,
      transform_exp NORMAL env exp,
      List.map (transform_prem env) prems
    )
  ) $ prod.at

let transform_deftyp env deftyp = 
  (match deftyp.it with
    | AliasT typ -> AliasT (Il.Eval.reduce_typ env (transform_typ NORMAL env typ))
    | StructT typfields -> StructT (List.map (fun (a, (bs, t, prems), hints) -> (a, (List.map (transform_bind env) bs, transform_typ NORMAL env t, List.map (transform_prem env) prems), hints)) typfields)
    | VariantT typcases -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> (m, (List.map (transform_bind env) bs, transform_typ NORMAL env t, List.map (transform_prem env) prems), hints)) typcases)
  ) $ deftyp.at

let transform_inst env inst =
  (match inst.it with 
    | (InstD (binds, args, deftyp)) when check_normal_type_creation inst -> 
      [InstD (List.map (transform_bind env) binds, List.map (transform_arg NORMAL env) args, transform_deftyp env deftyp) $ inst.at]
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
        InstD (List.map (transform_bind env) new_binds, List.map (transform_arg NORMAL env) new_args, transform_deftyp env new_deftyp) $ inst.at
      ) subst_list
  ) 

let rec transform_def env def = 
  (match def.it with
      | TypD (id, params, [inst]) when check_normal_type_creation inst -> TypD (id, params, transform_inst env inst)
      | TypD (id, params, insts) -> TypD (id, List.map (transform_param env) params, List.concat_map (transform_inst env) insts)
      | RecD defs -> RecD (List.map (transform_def env) defs)
      | RelD (id, m, typ, rules) -> RelD (id, m, transform_typ NORMAL env typ, List.map (transform_rule env) rules)
      | DecD (id, params, typ, clauses) -> DecD (id, List.map (transform_param env) params, transform_typ RETURN env typ, List.concat_map (transform_clause id env) clauses)
      | GramD (id, params, typ, prods) -> GramD (id, List.map (transform_param env) params, transform_typ NORMAL env typ, List.map (transform_prod env) prods)
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
        [TypD (id.it ^ sub_type_name binds $ id.at, List.map make_param_from_bind binds, [inst])]
    )

let rec transform_type_family def =
  (match def.it with
    | TypD (id, params, [inst]) when check_normal_type_creation inst -> [TypD (id, params, [inst])]
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