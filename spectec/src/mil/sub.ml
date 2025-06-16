(* open Il.Ast

let sub_hastable = Hashtbl.create 16

let rec get_sube_exp (exp : exp) =
  match exp.it with
    | UnE (_, e) -> get_sube_exp e
    | BinE (_, e1, e2) | CmpE (_, e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | TupE exps -> List.concat_map get_sube_exp exps
    | ProjE (e, _) -> get_sube_exp e
    | CaseE (_, e) -> get_sube_exp e
    | UncaseE (e, _) -> get_sube_exp e
    | OptE (Some e) -> get_sube_exp e
    | TheE e -> get_sube_exp e
    | StrE expfields -> List.concat_map (fun (_, e) -> get_sube_exp e) expfields
    | DotE (e, _) -> get_sube_exp e
    | CompE (e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | ListE exps -> List.concat_map get_sube_exp exps 
    | LenE e -> get_sube_exp e
    | CatE (e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | IdxE (e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | SliceE (e1, e2, e3) -> List.concat_map get_sube_exp [e1; e2; e3]
    | UpdE (e1, _, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | ExtE (e1, _, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | CallE (_, args) -> List.concat_map get_sube_arg args
    | IterE (e, _) -> get_sube_exp e
    | SubE _ as e -> [e $$ (exp.at, exp.note)]
    | _ -> []

and get_sube_arg (arg : arg) = 
  match arg.it with
    | ExpA e -> get_sube_exp e
    | TypA _ -> []

let rec get_sube_prem (premise : prem) =
  match premise.it with
    | RulePr (_, _, e) -> get_sube_exp e
    | IfPr e -> get_sube_exp e
    | IterPr (p, _) -> get_sube_prem p
    | _ -> []

let get_sube_rule (r : rule) =
  match r.it with
    | RuleD (_, _, _, e, prems) -> List.append (get_sube_exp e) (List.concat_map get_sube_prem prems)

let is_id_type (typ : typ) = 
  match typ.it with
    | VarT (_, args) -> args = []
    | _ -> false

let gen_typ_id (t : typ) =
  match t.it with
    | VarT (id, _) -> id
    | _ -> "" $ t.at

let rec is_same_type (t1 : typ) (t2 : typ) =
  match (t1.it, t2.it) with
    | VarT (id1, _), VarT (id2, _) -> id1.it = id2.it
    | NumT nt1, NumT nt2 -> nt1 = nt2
    | BoolT, BoolT -> true
    | TextT, TextT -> true
    | TupT tups, TupT tups2 -> (List.length tups) = (List.length tups2) && List.for_all2 (fun (_, t1') (_, t2') -> is_same_type t1' t2') tups tups2
    | IterT (t1', iter1), IterT (t2', iter2) -> iter1 = iter2 && is_same_type t1' t2'
    | _ -> false

(* Assumes that tuple variables will be in same order, can be modified if necessary *)
(* TODO must also check if some types inside the type are subtyppable and as such it should also be allowed *)
let rec find_same_typing (at : region) (m1 : ident) (t1 : typ) (t2_cases : sub_typ) =
  match t2_cases with
    | [] -> None
    | (_, m2, t2) as s_t :: _ when is_same_type t1 t2 && m1 = (transform_mixop m2) -> Some s_t
    | _ :: t2_cases' -> find_same_typing at m1 t1 t2_cases'

let get_num_tuple_typ (t : typ) = 
  match t.it with
    | TupT tups -> List.length tups 
    | _ -> 0

let transform_sub_types (at : region) (t1_id : id) (t2_id : id) (t1_cases : sub_typ) (t2_cases : sub_typ) =
  let func_name = func_prefix ^ coerce_prefix ^ transform_id t1_id ^ "__" ^ transform_id t2_id in 
  
  [Right (DefinitionD (func_name, 
    [(var_prefix ^ transform_id t1_id, T_ident [transform_id t1_id])],
    T_ident [transform_id t2_id], List.map (fun (id, m1, t1) ->
      let s_t = find_same_typing at (transform_mixop m1) t1 t2_cases in
      match s_t with
        | Some (id2, m2, _) ->
          let var_list = List.init (get_num_tuple_typ t1) (fun i -> T_ident [var_prefix ^ string_of_int i]) in
          (T_app (T_ident [transform_id id; transform_mixop m1], var_list),
          T_app (T_ident [transform_id id2; transform_mixop m2], var_list))
        | None -> (T_ident [""], T_ident [""])
    ) t1_cases) $ at  ); 
  Right (CoercionD (func_name, transform_id t1_id, transform_id t2_id) $ at )]

(* TODO can be extended to other defs if necessary *)
let rec transform_sub_def (env : env) (d : def) = 
  match d.it with
    | RelD (_, _, _, rules) -> let sub_expressions = List.concat_map get_sube_rule rules in
      List.append (List.concat_map (fun e -> match e.it with 
        | SubE (_, t1, t2) when is_id_type t1 && is_id_type t2 -> 
          let (t1_id, t2_id) = (gen_typ_id t1, gen_typ_id t2) in
          let combined_name = (t1_id.it ^ "__" ^ t2_id.it) in 
          if (Hashtbl.mem sub_hastable combined_name) then []
          else (let typ1_cases = find "Sub pass" env.subs t1_id in
            let typ2_cases = find "Sub pass" env.subs t2_id in
            Hashtbl.add sub_hastable combined_name combined_name;
            transform_sub_types d.at t1_id t2_id typ1_cases typ2_cases)
        | _ -> []) sub_expressions) [Left d]
    | RecD defs -> let flat_list = List.concat_map (transform_sub_def env) defs in
      let (defs, coq_defs) = partition_eitherlist flat_list in
      (List.map Either.right coq_defs) @ [Left (RecD defs $ d.at)]
    | _ -> [Left d]

let transform_sub (e : env) (il : script) =
  List.concat_map (transform_sub_def e) il *)