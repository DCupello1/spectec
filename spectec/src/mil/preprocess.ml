open Il.Ast
open Il
open Util.Source
(* 
Some MIL-specific passes that add some helper functions
for Uncase and well-formed predicates
*)

module StringMap = Map.Make(String)
module IntSet = Set.Make(Int)
type uncase_map = (IntSet.t) StringMap.t

let rec preprocess_iter uncase_map i =
  match i with 
    | ListN (exp, id_opt) -> ListN (preprocess_exp uncase_map exp, id_opt)
    | _ -> i

and preprocess_typ uncase_map t = 
  (match t.it with
    | VarT (id, args) -> VarT (id, List.map (preprocess_arg uncase_map) args)
    | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (preprocess_exp uncase_map e, preprocess_typ uncase_map t)) exp_typ_pairs)
    | IterT (typ, iter) -> IterT (preprocess_typ uncase_map typ, preprocess_iter uncase_map iter)
    | typ -> typ
  ) $ t.at

and preprocess_exp uncase_map e = 
  let p_func = preprocess_exp uncase_map in
  (match e.it with
    (* | ProjE ({ it = UncaseE(e, _); _}, n) -> e.it *)
    | UnE (unop, optyp, e1) -> UnE (unop, optyp, p_func e1)
    | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, p_func e1, p_func e2)
    | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, p_func e1, p_func e2)
    | TupE (exps) -> TupE (List.map p_func exps)
    | ProjE (e1, n) -> ProjE (p_func e1, n)
    | CaseE (m, e1) -> CaseE (m, p_func e1)
    | UncaseE (e1, m) -> UncaseE (p_func e1, m)
    | OptE e1 -> OptE (Option.map p_func e1)
    | TheE e1 -> TheE (p_func e1)
    | StrE fields -> StrE (List.map (fun (a, e1) -> (a, p_func e1)) fields)
    | DotE (e1, a) -> DotE (p_func e1, a)
    | CompE (e1, e2) -> CompE (p_func e1, p_func e2)
    | ListE entries -> ListE (List.map p_func entries)
    | LiftE e1 -> LiftE (p_func e1)
    | MemE (e1, e2) -> MemE (p_func e1, p_func e2)
    | LenE e1 -> LenE e1
    | CatE (e1, e2) -> CatE (p_func e1, p_func e2)
    | IdxE (e1, e2) -> IdxE (p_func e1, p_func e2)
    | SliceE (e1, e2, e3) -> SliceE (p_func e1, p_func e2, p_func e3)
    | UpdE (e1, p, e2) -> UpdE (p_func e1, p, p_func e2)
    | ExtE (e1, p, e2) -> ExtE (p_func e1, p, p_func e2)
    | CallE (id, args) -> CallE (id, List.map (preprocess_arg uncase_map) args)
    | IterE (e1, (iter, id_exp_pairs)) -> IterE (p_func e1, (preprocess_iter uncase_map iter, List.map (fun (id, exp) -> (id, p_func exp)) id_exp_pairs))
    | CvtE (e1, nt1, nt2) -> CvtE (p_func e1, nt1, nt2)
    | SubE (e1, t1, t2) -> SubE (p_func e1, preprocess_typ uncase_map t1, preprocess_typ uncase_map t2)
    | exp -> exp
  ) $$ e.at % (preprocess_typ uncase_map e.note)

and preprocess_sym uncase_map s = 
  (match s.it with
    | VarG (id, args) -> VarG (id, List.map (preprocess_arg uncase_map) args)
    | SeqG syms | AltG syms -> SeqG (List.map (preprocess_sym uncase_map) syms)
    | RangeG (syml, symu) -> RangeG (preprocess_sym uncase_map syml, preprocess_sym uncase_map symu)
    | IterG (sym, (iter, id_exp_pairs)) -> IterG (preprocess_sym uncase_map sym, (preprocess_iter uncase_map iter, 
        List.map (fun (id, exp) -> (id, preprocess_exp uncase_map exp)) id_exp_pairs)
      )
    | AttrG (e, sym) -> AttrG (preprocess_exp uncase_map e, preprocess_sym uncase_map sym)
    | sym -> sym 
  ) $ s.at 

and preprocess_arg uncase_map a =
  (match a.it with
    | ExpA exp -> ExpA (preprocess_exp uncase_map exp)
    | TypA typ -> TypA (preprocess_typ uncase_map typ)
    | DefA id -> DefA id
    | GramA sym -> GramA (preprocess_sym uncase_map sym)
  ) $ a.at

and preprocess_bind uncase_map b =
  (match b.it with
    | ExpB (id, typ) -> ExpB (id, preprocess_typ uncase_map typ)
    | TypB id -> TypB id
    | DefB (id, params, typ) -> DefB (id, List.map (preprocess_param uncase_map) params, preprocess_typ uncase_map typ)
    | GramB (id, params, typ) -> GramB (id, List.map (preprocess_param uncase_map) params, preprocess_typ uncase_map typ)
  ) $ b.at 
  
and preprocess_param uncase_map p =
  (match p.it with
    | ExpP (id, typ) -> ExpP (id, preprocess_typ uncase_map typ)
    | TypP id -> TypP id
    | DefP (id, params, typ) -> DefP (id, List.map (preprocess_param uncase_map) params, preprocess_typ uncase_map typ)
    | GramP (id, typ) -> GramP (id, preprocess_typ uncase_map typ)
  ) $ p.at 

let rec preprocess_prem uncase_map prem = 
  (match prem.it with
    | RulePr (id, m, e) -> RulePr (id, m, preprocess_exp uncase_map e)
    | IfPr e -> IfPr (preprocess_exp uncase_map e)
    | LetPr (e1, e2, ids) -> LetPr (preprocess_exp uncase_map e1, preprocess_exp uncase_map e2, ids)
    | ElsePr -> ElsePr
    | IterPr (prem1, (iter, id_exp_pairs)) -> IterPr (preprocess_prem uncase_map prem1, 
        (preprocess_iter uncase_map iter, List.map (fun (id, exp) -> (id, preprocess_exp uncase_map exp)) id_exp_pairs)
      )
  ) $ prem.at

let preprocess_inst uncase_map inst = 
  (match inst.it with
    | InstD (binds, args, deftyp) -> InstD (List.map (preprocess_bind uncase_map) binds, List.map (preprocess_arg uncase_map) args, 
      (match deftyp.it with 
        | AliasT typ -> AliasT (preprocess_typ uncase_map typ)
        | StructT typfields -> StructT (List.map (fun (a, (c_binds, typ, prems), hints) -> 
            (a, (List.map (preprocess_bind uncase_map) c_binds, preprocess_typ uncase_map typ, List.map (preprocess_prem uncase_map) prems), hints)  
          ) typfields)
        | VariantT typcases -> VariantT (List.map (fun (m, (c_binds, typ, prems), hints) -> 
            (m, (List.map (preprocess_bind uncase_map) c_binds, preprocess_typ uncase_map typ, List.map (preprocess_prem uncase_map) prems), hints)  
          ) typcases)
      ) $ deftyp.at
    )
  ) $ inst.at

let preprocess_rule uncase_map rule = 
  (match rule.it with
    | RuleD (id, binds, m, exp, prems) -> RuleD (id, 
      List.map (preprocess_bind uncase_map) binds, 
      m, 
      preprocess_exp uncase_map exp, 
      List.map (preprocess_prem uncase_map) prems
    )
  ) $ rule.at

let preprocess_clause uncase_map clause =
  (match clause.it with 
    | DefD (binds, args, exp, prems) -> DefD (List.map (preprocess_bind uncase_map) binds, 
      List.map (preprocess_arg uncase_map) args,
      preprocess_exp uncase_map exp, 
      List.map (preprocess_prem uncase_map) prems
    )
  ) $ clause.at

let preprocess_prod uncase_map prod = 
  (match prod.it with 
    | ProdD (binds, sym, exp, prems) -> ProdD (List.map (preprocess_bind uncase_map) binds,
      preprocess_sym uncase_map sym,
      preprocess_exp uncase_map exp,
      List.map (preprocess_prem uncase_map) prems
    )
  ) $ prod.at

let rec preprocess_def uncase_map def = 
  (match def.it with
    | TypD (id, params, insts) -> TypD (id, List.map (preprocess_param uncase_map) params, List.map (preprocess_inst uncase_map) insts)
    | RelD (id, m, typ, rules) -> RelD (id, m, preprocess_typ uncase_map typ, List.map (preprocess_rule uncase_map) rules)
    | DecD (id, params, typ, clauses) -> DecD (id, List.map (preprocess_param uncase_map) params, preprocess_typ uncase_map typ, List.map (preprocess_clause uncase_map) clauses)
    | GramD (id, params, typ, prods) -> GramD (id, List.map (preprocess_param uncase_map) params, preprocess_typ uncase_map typ, List.map (preprocess_prod uncase_map) prods)
    | RecD defs -> RecD (List.map (preprocess_def uncase_map) defs)
    | HintD hintdef -> HintD hintdef
  ) $ def.at 

let collect_uncase_iter(): uncase_map ref * (module Iter.Arg) =
  let module Arg = 
    struct
      include Iter.Skip 
      let acc = ref StringMap.empty
      let visit_exp (exp : exp) = 
        match exp.it with
          | ProjE ({ it = UncaseE(e, _); _}, n) -> 
            let typ_name = Print.string_of_typ_name e.note in
            acc := StringMap.update typ_name (fun int_set_opt -> match int_set_opt with 
              | None -> Some (IntSet.singleton n)
              | Some int_set -> Some (IntSet.add n int_set)
            ) !acc
          | _ -> ()
    end
  in Arg.acc, (module Arg)

let preprocess (il : script): script =
  let acc, (module Arg : Iter.Arg) = collect_uncase_iter() in
  let module Acc = Iter.Make(Arg) in
  List.iter Acc.def il;
  List.map (preprocess_def !acc) il