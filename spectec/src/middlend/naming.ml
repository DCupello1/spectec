open Il.Ast
open Il
open Util.Source
(* open Util *)
open Xl.Atom

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let error at msg = Util.Error.error at "naming" msg  

type env = {
  prefix_map : (string list) StringMap.t;
  il_env : Il.Env.t;
}

let reserved_ids = ["N"; "in"; "In"; 
                    "S";
                    "return";
                    "if";
                    "bool";
                    "prod";
                    "()"; "tt"; 
                    "Import"; "Export"; 
                    "List"; "String"; 
                    "Type"; "list"; "nat"] |> Env.Set.of_list

let (let*) = Option.bind
let make_prefix = "mk_"
let var_prefix = "v_"
let fun_prefix = "fun_"
let res_prefix = "res_"

type id_type = VAR | USERDEF | FUNCDEF
let empty_info: region * Xl.Atom.info = (no_region, {def = ""; case = ""})

(* Id transformation *)
let transform_id' env (id_type : id_type) (s : text) = 
  let change_id s' = 
    String.map (function
     | '.' -> '_'
     | '-' -> '_'
     | c -> c
    ) s'
    (* This suffixes any '*' with '_lst' and '?' with '_opt' for clarity *)
    |> Str.global_replace (Str.regexp {|\(*\)|}) "_lst"
    |> Util.Lib.String.replace "?" "_opt"
  in
  let s' = change_id s in
  match id_type with
  | VAR when Il.Env.mem_typ env (s' $ no_region) || Il.Env.Set.mem s' reserved_ids -> var_prefix ^ s'
  | FUNCDEF when Il.Env.mem_typ env (s' $ no_region) 
    || Il.Env.mem_rel env (s' $ no_region) 
    || Il.Env.Set.mem s reserved_ids -> fun_prefix ^ s' 
  | USERDEF when Il.Env.Set.mem s reserved_ids -> res_prefix ^ s'
  | _ -> s'

let transform_var_id env id = transform_id' env VAR id.it $ id.at
let transform_fun_id env id = transform_id' env FUNCDEF id.it $ id.at
let transform_user_def_id env id = transform_id' env USERDEF id.it $ id.at
let transform_rule_id env prefix rule_id rel_id = 
  match rule_id.it, prefix with
  | "", "" -> make_prefix ^ rel_id.it
  | _ -> prefix ^ transform_id' env USERDEF rule_id.it

(* Atom functions *)
let transform_atom env a = 
  match a.it with
  | Atom s -> Atom (transform_user_def_id env (s $ a.at)).it $$ a.at % a.note
  | _ -> a

let transform_mixop env typ_id (m : mixop) = 
  match m with
  | [[]; []] -> [[(Atom (make_prefix ^ typ_id.it) $$ empty_info)]; []]
  | _ -> List.map (fun inner_m -> List.map (transform_atom env) inner_m) m

let prepend_atom prefix a =
  if prefix = "" then a else
  match a.it with
  | Atom s -> Atom (prefix ^ s) $$ a.at % a.note
  | _ -> a

let prepend_mixop prefix m =
  if prefix = "" then m else
  match m with
  | m' :: ms -> ((Atom prefix $$ empty_info) :: m') :: ms
  | [] -> []

let check_inst_mixop m inst = 
  match inst.it with
  | InstD (_, _, {it = VariantT typcases; _}) -> List.exists (fun (m', _, _) -> Eq.eq_mixop m m') typcases
  | _ -> false

let check_inst_fields fields inst = 
  match inst.it with
  | InstD (_, _, {it = StructT typfields; _}) when List.length typfields = List.length fields -> 
    List.for_all2 (fun (a', _, _) (a, _) -> Eq.eq_atom a a') typfields fields
  | _ -> false

let check_inst_atom a inst = 
  match inst.it with
  | InstD (_, _, {it = StructT typfields; _}) -> 
    List.exists (fun (a', _, _) -> Eq.eq_atom a a') typfields
  | _ -> false
  
let rec check_iteration_naming e iterexp = 
  match e.it, iterexp with
  | VarE id, (_, [(id', _)]) -> Eq.eq_id id id'
  | IterE (e, ((_, [(_, {it = VarE id; _})]) as i)), (_, [(id', _)]) -> Eq.eq_id id id' && check_iteration_naming e i
  | _ -> false 

let rec transform_iter env i =
  match i with 
  | ListN (exp, id_opt) -> ListN (transform_exp env exp, id_opt)
  | _ -> i

and transform_typ env t = 
  (match t.it with
  | VarT (id, args) -> VarT (transform_user_def_id env.il_env id, List.map (transform_arg env) args)
  | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (transform_exp env e, transform_typ env t)) exp_typ_pairs)
  | IterT (typ, iter) -> IterT (transform_typ env typ, transform_iter env iter)
  | typ -> typ
  ) $ t.at

and apply_prefix_mixop env m name at = 
  let* (_, insts) = Env.find_opt_typ env.il_env (name $ at) in
  let* idx = List.find_index (check_inst_mixop m) insts in 
  let* prefixes = StringMap.find_opt name env.prefix_map in
  let* prefix = List.nth_opt prefixes idx in 
  Some (prepend_mixop prefix m |> transform_mixop env.il_env (name $ at))  

and apply_prefix_fields env fields name at =
  let* (_, insts) = Env.find_opt_typ env.il_env (name $ at) in
  let* idx = List.find_index (check_inst_fields fields) insts in 
  let* prefixes = StringMap.find_opt name env.prefix_map in
  let* prefix = List.nth_opt prefixes idx in
  Some (StrE (List.map (fun (a, e1) -> (prepend_atom prefix a |> transform_atom env.il_env, transform_exp env e1)) fields))

and apply_prefix_atom env a name at =
  let* (_, insts) = Env.find_opt_typ env.il_env (name $ at) in
  let* idx = List.find_index (check_inst_atom a) insts in 
  let* prefixes = StringMap.find_opt name env.prefix_map in
  let* prefix = List.nth_opt prefixes idx in
  Some (prepend_atom prefix a |> transform_atom env.il_env)

and transform_exp env e = 
  let t_func = transform_exp env in
  (match e.it with
  (* Improve naming of variables and functions *)
  | VarE id -> VarE (transform_var_id env.il_env id)
  | CallE (id, args) -> CallE (transform_fun_id env.il_env id, List.map (transform_arg env) args)

  (* Apply prefixes to corresponding expressions*)
  | CaseE (m, e1) -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env e.note) in
    let t_m = transform_mixop env.il_env (id $ e.at) m in
    let m' = Option.value (apply_prefix_mixop env m id e.at) ~default:t_m in
    CaseE(m', t_func e1)

  | StrE fields -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env e.note) in
    let t_fields = List.map (fun (a, e1) -> (transform_atom env.il_env a, t_func e1)) fields in
    let exp = StrE t_fields in
    Option.value (apply_prefix_fields env t_fields id e.at) ~default:exp

  | UncaseE (e1, m) -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env e.note) in
    let t_m = transform_mixop env.il_env (id $ e.at) m in
    let m' = Option.value (apply_prefix_mixop env m id e.at) ~default:t_m in
    UncaseE (t_func e1, m')
  
  | DotE (e1, a) -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env e1.note) in
    let t_a = transform_atom env.il_env a in
    let a' = Option.value (apply_prefix_atom env a id e.at) ~default:t_a in
    DotE (t_func e1, a')
  
  (* Special case for iteration naming - just use the variable it is iterating on *)
  | IterE (e, ((_, [(_, {it = VarE id''; _})]) as iterexp)) when check_iteration_naming e iterexp -> 
    VarE (transform_var_id env.il_env id'')
  
  (* Boilerplate Traversal *)
  | UnE (unop, optyp, e1) -> UnE (unop, optyp, t_func e1)
  | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2)
  | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2)
  | TupE (exps) -> TupE (List.map t_func exps)
  | ProjE (e1, n) -> ProjE (t_func e1, n)
  | OptE e1 -> OptE (Option.map t_func e1)
  | TheE e1 -> TheE (t_func e1)
  | CompE (e1, e2) -> CompE (t_func e1, t_func e2)
  | ListE entries -> ListE (List.map t_func entries)
  | LiftE e1 -> LiftE (t_func e1)
  | MemE (e1, e2) -> MemE (t_func e1, t_func e2)
  | LenE e1 -> LenE (t_func e1)
  | CatE (e1, e2) -> CatE (t_func e1, t_func e2)
  | IdxE (e1, e2) -> IdxE (t_func e1, t_func e2)
  | SliceE (e1, e2, e3) -> SliceE (t_func e1, t_func e2, t_func e3)
  | UpdE (e1, p, e2) -> UpdE (t_func e1, transform_path env p, t_func e2)
  | ExtE (e1, p, e2) -> ExtE (t_func e1, transform_path env p, t_func e2)
  | IterE (e1, (iter, id_exp_pairs)) -> IterE (t_func e1, (transform_iter env iter, List.map (fun (id', exp) -> (transform_var_id env.il_env id', t_func exp)) id_exp_pairs))
  | CvtE (e1, nt1, nt2) -> CvtE (t_func e1, nt1, nt2)
  | SubE (e1, t1, t2) -> SubE (t_func e1, transform_typ env t1, transform_typ env t2)
  | exp -> exp
  ) $$ e.at % (transform_typ env e.note)

and transform_path env path = 
  (match path.it with
  | RootP -> RootP
  | IdxP (p, e) -> IdxP (transform_path env p, transform_exp env e)
  | SliceP (p, e1, e2) -> SliceP (transform_path env p, transform_exp env e1, transform_exp env e2)
  | DotP (p, a) -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env p.note) in
    let t_a = transform_atom env.il_env a in
    let a' = Option.value (apply_prefix_atom env a id path.at) ~default:t_a in
    DotP (transform_path env p, a')
  ) $$ path.at % (transform_typ env path.note)

and transform_sym env s = 
  (match s.it with
  | VarG (id, args) -> VarG (id, List.map (transform_arg env) args)
  | SeqG syms | AltG syms -> SeqG (List.map (transform_sym env) syms)
  | RangeG (syml, symu) -> RangeG (transform_sym env syml, transform_sym env symu)
  | IterG (sym, (iter, id_exp_pairs)) -> IterG (transform_sym env sym, (transform_iter env iter, 
      List.map (fun (id, exp) -> (transform_var_id env.il_env id, transform_exp env exp)) id_exp_pairs)
    )
  | AttrG (e, sym) -> AttrG (transform_exp env e, transform_sym env sym)
  | sym -> sym 
  ) $ s.at 

and transform_arg env a =
  (match a.it with
  | ExpA exp -> ExpA (transform_exp env exp)
  | TypA typ -> TypA (transform_typ env typ)
  | DefA id -> DefA (transform_fun_id env.il_env id)
  | GramA sym -> GramA (transform_sym env sym)
  ) $ a.at

and transform_bind env b =
  (match b.it with
  | ExpB (id, typ) -> ExpB (transform_var_id env.il_env id, transform_typ env typ)
  | TypB id -> TypB (transform_var_id env.il_env id)
  | DefB (id, params, typ) -> DefB (transform_fun_id env.il_env id, List.map (transform_param env) params, transform_typ env typ)
  | GramB (id, params, typ) -> GramB (id, List.map (transform_param env) params, transform_typ env typ)
  ) $ b.at 
  
and transform_param env p =
  (match p.it with
  | ExpP (id, typ) -> ExpP (transform_var_id env.il_env id, transform_typ env typ)
  | TypP id -> TypP (transform_var_id env.il_env id)
  | DefP (id, params, typ) -> DefP (id, List.map (transform_param env) params, transform_typ env typ)
  | GramP (id, typ) -> GramP (id, transform_typ env typ)
  ) $ p.at 

let rec transform_prem env prem = 
  (match prem.it with
  | RulePr (id, m, e) -> RulePr (transform_user_def_id env.il_env id, m, transform_exp env e)
  | IfPr e -> IfPr (transform_exp env e)
  | LetPr (e1, e2, ids) -> LetPr (transform_exp env e1, transform_exp env e2, ids)
  | ElsePr -> ElsePr
  | IterPr (prem1, (iter, id_exp_pairs)) -> IterPr (transform_prem env prem1, 
      (transform_iter env iter, List.map (fun (id, exp) -> (transform_var_id env.il_env id, transform_exp env exp)) id_exp_pairs)
    )
  | NegPr p -> NegPr (transform_prem env p)
  ) $ prem.at

let transform_inst env id prefix inst = 
  (match inst.it with
  | InstD (binds, args, deftyp) -> InstD (List.map (transform_bind env) binds, List.map (transform_arg env) args, 
    (match deftyp.it with 
    | AliasT typ -> AliasT (transform_typ env typ)
    | StructT typfields -> StructT (List.map (fun (a, (c_binds, typ, prems), hints) ->
        (prepend_atom prefix a |> transform_atom env.il_env, 
        (List.map (transform_bind env) c_binds, transform_typ env typ, List.map (transform_prem env) prems), hints)  
      ) typfields)
    | VariantT typcases -> 
      VariantT (List.map (fun (m, (c_binds, typ, prems), hints) -> 
        (prepend_mixop prefix m |> transform_mixop env.il_env id, 
        (List.map (transform_bind env) c_binds, transform_typ env typ, List.map (transform_prem env) prems), hints)  
      ) typcases)
    ) $ deftyp.at
  )
  ) $ inst.at

let transform_rule env rel_id prefix rule = 
  (match rule.it with
  | RuleD (id, binds, m, exp, prems) -> 
    RuleD (transform_rule_id env.il_env prefix id rel_id $ id.at, 
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

let rec transform_def env def = 
  (match def.it with
  | TypD (id, params, insts) -> 
    let prefixes = (match (StringMap.find_opt id.it env.prefix_map) with
    | Some s -> s
    | _ -> []
    ) in
    let prefix_length = List.length prefixes in
    let insts_length = List.length insts in
    if (prefix_length > insts_length) then error def.at "Too many prefixes" else
    let extra_prefixes = List.init (insts_length - prefix_length) (fun _ -> "") in
    TypD (transform_user_def_id env.il_env id, List.map (transform_param env) params, List.map2 (transform_inst env id) (prefixes @ extra_prefixes) insts)
  | RelD (id, m, typ, rules) -> 
    let prefix = (match (StringMap.find_opt id.it env.prefix_map) with
    | Some [s] -> s
    | None -> ""
    | _ -> error def.at "Too many prefixes"
    ) in
    RelD (transform_user_def_id env.il_env id, m, transform_typ env typ, List.map (transform_rule env id prefix) rules)
  | DecD (id, params, typ, clauses) -> DecD (transform_fun_id env.il_env id, List.map (transform_param env) params |> Utils.improve_ids_params, transform_typ env typ, List.map (transform_clause env) clauses)
  | GramD (id, params, typ, prods) -> GramD (id, List.map (transform_param env) params, transform_typ env typ, List.map (transform_prod env) prods)
  | RecD defs -> RecD (List.map (transform_def env) defs)
  | HintD hintdef -> HintD hintdef
  ) $ def.at

(* Making prefix map *)

let get_text_exp = function
  | {it = El.Ast.TextE s; _} -> s
  | {at; _}  -> error at "malformed prefix hint"

let list_of_prefix = function
  | {it = El.Ast.TextE s; _} -> [s]
  | {it = El.Ast.SeqE exps; _} -> List.map get_text_exp exps 
  | ({at; _} as e) -> error at ("malformed prefix hint: " ^ El.Print.string_of_exp e)

let register_prefix map id el_exp =
  map := StringMap.add id.it (list_of_prefix el_exp) !map

let has_prefix_hint (hint : hint) = hint.hintid.it = "prefix"

let create_prefix_map_def map (d : def) = 
  match d.it with
    | HintD {it = TypH (id, hints); _}
    | HintD {it = RelH (id, hints); _} ->
      (match (List.find_opt has_prefix_hint hints) with
      | Some h -> register_prefix map id h.hintexp
      | _ -> ()
      ) 
    | _ -> ()

let create_prefix_map (il : script) = 
  let map = ref StringMap.empty in
  List.iter (create_prefix_map_def map) il;
  !map

let create_env il = {
  prefix_map = create_prefix_map il;
  il_env = Env.env_of_script il
}

let transform (il : script): script =
  let env = create_env il in 
  List.map (transform_def env) il