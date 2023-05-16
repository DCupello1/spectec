open Util
open Ast
open Source

let id_fold x acc = (x, acc)

let traverse_phrase traverse p trv acc =
  let it, acc' = traverse p.it trv acc in
  ({ p with it }, acc')

let traverse2 tx1 tx2 trv acc =
  let x1', acc' = tx1 trv acc in
  let x2', acc'' = tx2 trv acc' in
  ((x1', x2'), acc'')

let traverse3 tx1 tx2 tx3 trv acc =
  let x1', acc' = tx1 trv acc in
  let x2', acc'' = tx2 trv acc' in
  let x3', acc''' = tx3 trv acc'' in
  ((x1', x2', x3'), acc''')

let traverse4 tx1 tx2 tx3 tx4 trv acc =
  let x1', acc' = tx1 trv acc in
  let x2', acc'' = tx2 trv acc' in
  let x3', acc''' = tx3 trv acc'' in
  let x4', acc'''' = tx4 trv acc''' in
  ((x1', x2', x3', x4'), acc'''')

let rec traverse_list f ds trv acc =
  match ds with
  | [] -> ([], acc)
  | d :: ds ->
      let d', acc' = f d trv acc in
      let ds', acc'' = traverse_list f ds trv acc' in
      (d' :: ds', acc'')

let traverse_option f eo trv acc =
  match eo with
  | None -> (None, acc)
  | Some e ->
      let e', acc' = f e trv acc in
      (Some e', acc')

let rec traverse_fieldlist f es trv acc =
  match es with
  | [] -> ([], acc)
  | (x, e) :: es ->
      let e', acc' = f e trv acc in
      let es', acc'' = traverse_fieldlist f es trv acc' in
      ((x, e') :: es', acc'')

type 'acc t = {
  exp : exp -> 'acc -> exp * 'acc;
  iter : iter -> 'acc -> iter * 'acc;
  iterexp : iterexp -> 'acc -> iterexp * 'acc;
  path : path -> 'acc -> path * 'acc;
  def : def -> 'acc -> def * 'acc;
}

let id () =
  {
    exp = id_fold;
    iter = id_fold;
    iterexp = id_fold;
    path = id_fold;
    def = id_fold;
  }

let rec traverse_exp e trv acc =
  let e', acc' = traverse_phrase traverse_exp' e trv acc in
  trv.exp e' acc'

and traverse_exp' exp' trv acc =
  match exp' with
  | VarE x -> (VarE x, acc)
  | BoolE b -> (BoolE b, acc)
  | NatE n -> (NatE n, acc)
  | TextE tx -> (TextE tx, acc)
  | UnE (op, e) ->
      let e', acc' = traverse_exp e trv acc in
      (UnE (op, e'), acc')
  | BinE (op, e1, e2) ->
      let (e1', e2'), acc' =
        traverse2 (traverse_exp e1) (traverse_exp e2) trv acc
      in
      (BinE (op, e1', e2'), acc')
  | CmpE (op, e1, e2) ->
      let (e1', e2'), acc' =
        traverse2 (traverse_exp e1) (traverse_exp e2) trv acc
      in
      (CmpE (op, e1', e2'), acc')
  | IdxE (e1, e2) ->
      let (e1', e2'), acc' =
        traverse2 (traverse_exp e1) (traverse_exp e2) trv acc
      in
      (IdxE (e1', e2'), acc')
  | SliceE (e1, e2, e3) ->
      let (e1', e2', e3'), acc' =
        traverse3 (traverse_exp e1) (traverse_exp e2) (traverse_exp e3) trv acc
      in
      (SliceE (e1', e2', e3'), acc')
  | UpdE (e1, p, e2) ->
      let (e1', p', e2'), acc' =
        traverse3 (traverse_exp e1) (traverse_path p) (traverse_exp e2) trv acc
      in
      (UpdE (e1', p', e2'), acc')
  | ExtE (e1, p, e2) ->
      let (e1', p', e2'), acc' =
        traverse3 (traverse_exp e1) (traverse_path p) (traverse_exp e2) trv acc
      in
      (ExtE (e1', p', e2'), acc')
  | StrE es ->
      let es', acc' = traverse_fieldlist traverse_exp es trv acc in
      (StrE es', acc')
  | DotE (e, x) ->
      let e', acc' = traverse_exp e trv acc in
      (DotE (e', x), acc')
  | CompE (e1, e2) ->
      let (e1', e2'), acc' =
        traverse2 (traverse_exp e1) (traverse_exp e2) trv acc
      in
      (CompE (e1', e2'), acc')
  | LenE e ->
      let e', acc' = traverse_exp e trv acc in
      (LenE e', acc')
  | TupE es ->
      let es', acc' = traverse_list traverse_exp es trv acc in
      (TupE es', acc')
  | MixE (op, e) ->
      let e', acc' = traverse_exp e trv acc in
      (MixE (op, e'), acc')
  | CallE (x, e) ->
      let e', acc' = traverse_exp e trv acc in
      (CallE (x, e'), acc')
  | IterE (e, ie) ->
      let (e', ie'), acc' =
        traverse2 (traverse_exp e) (traverse_iterexp ie) trv acc
      in
      (IterE (e', ie'), acc')
  | OptE eo ->
      let eo', acc' = traverse_option traverse_exp eo trv acc in
      (OptE eo', acc')
  | TheE e ->
      let e', acc' = traverse_exp e trv acc in
      (TheE e', acc')
  | ListE es ->
      let es', acc' = traverse_list traverse_exp es trv acc in
      (ListE es', acc')
  | CatE (e1, e2) ->
      let (e1', e2'), acc' =
        traverse2 (traverse_exp e1) (traverse_exp e2) trv acc
      in
      (CatE (e1', e2'), acc')
  | CaseE (x, e) ->
      let e', acc' = traverse_exp e trv acc in
      (CaseE (x, e'), acc')
  | SubE (e, t1, t2) ->
      let e', acc' = traverse_exp e trv acc in
      (SubE (e', t1, t2), acc')

and traverse_iterexp (ie, vs) trv acc =
  let ie', acc' = traverse_iter ie trv acc in
  ((ie', vs), acc')

and traverse_iter ie trv acc =
  match ie with
  | Opt -> (Opt, acc)
  | List -> (List, acc)
  | List1 -> (List1, acc)
  | ListN e ->
      let e', acc' = traverse_exp e trv acc in
      (ListN e', acc')

and traverse_path p trv acc =
  let p', acc' = traverse_path' p.it trv acc in
  ({ p with it = p' }, acc')

and traverse_path' p trv acc =
  match p with
  | RootP -> (RootP, acc)
  | IdxP (p, e) ->
      let (p', e'), acc' =
        traverse2 (traverse_path p) (traverse_exp e) trv acc
      in
      (IdxP (p', e'), acc')
  | SliceP (p, e1, e2) ->
      let (p', e1', e2'), acc' =
        traverse3 (traverse_path p) (traverse_exp e1) (traverse_exp e2) trv acc
      in
      (SliceP (p', e1', e2'), acc')
  | DotP (p, a) ->
      let p', acc' = traverse_path p trv acc in
      (DotP (p', a), acc')

let traverse_bind (x, t, iters) trv acc =
  let iters', acc' = traverse_list traverse_iter iters trv acc in
  ((x, t, iters'), acc')

let traverse_binds bs trv acc =
  let bs', acc' = traverse_list traverse_bind bs trv acc in
  (bs', acc')

let rec traverse_def d trv acc =
  let d', acc' = traverse_phrase traverse_def' d trv acc in
  trv.def d' acc'

and traverse_def' def' trv acc =
  match def' with
  | SynD (x, t) -> (SynD (x, t), acc)
  | RelD (x, op, t, rs) ->
      let rs', acc' = traverse_list traverse_rule rs trv acc in
      (RelD (x, op, t, rs'), acc')
  | DecD (x, t1, t2, cs) ->
      let cs', acc' = traverse_list traverse_clause cs trv acc in
      (DecD (x, t1, t2, cs'), acc')
  | RecD ds ->
      let ds', acc' = traverse_list traverse_def ds trv acc in
      (RecD ds', acc')
  | HintD hd -> (HintD hd, acc)

and traverse_rule r trv acc = traverse_phrase traverse_rule' r trv acc

and traverse_rule' r trv acc =
  match r with
  | RuleD (x, bs, op, e, ps) ->
      let (bs', e', ps'), acc' =
        traverse3 (traverse_binds bs) (traverse_exp e)
          (traverse_list traverse_premise ps)
          trv acc
      in
      (RuleD (x, bs', op, e', ps'), acc')

and traverse_clause c trv acc = traverse_phrase traverse_clause' c trv acc

and traverse_clause' c trv acc =
  match c with
  | DefD (bs, e1, e2, ps) ->
      let (bs', e1', e2', ps'), acc' =
        traverse4 (traverse_binds bs) (traverse_exp e1) (traverse_exp e2)
          (traverse_list traverse_premise ps)
          trv acc
      in
      (DefD (bs', e1', e2', ps'), acc')

and traverse_premise p trv acc = traverse_phrase traverse_premise' p trv acc

and traverse_premise' p trv acc =
  match p with
  | RulePr (x, op, e) ->
      let e', acc' = traverse_exp e trv acc in
      (RulePr (x, op, e'), acc')
  | IfPr e ->
      let e', acc' = traverse_exp e trv acc in
      (IfPr e', acc')
  | ElsePr -> (ElsePr, acc)
  | IterPr (p, ie) ->
      let (p', ie'), acc' =
        traverse2 (traverse_premise p) (traverse_iterexp ie) trv acc
      in
      (IterPr (p', ie'), acc')

and traverse_hintdef hd trv acc = traverse_phrase traverse_hintdef' hd trv acc

and traverse_hintdef' hs _trv acc =
  match hs with
  | SynH (x, hs) -> (SynH (x, hs), acc)
  | RelH (x, hs) -> (RelH (x, hs), acc)
  | DecH (x, hs) -> (DecH (x, hs), acc)

let traverse_script s trv acc =
  let s', acc' = traverse_list traverse_def s trv acc in
  (s', acc')

let traverse traverse ?(exp = id_fold) ?(iter = id_fold) ?(iterexp = id_fold)
    ?(path = id_fold) ?(def = id_fold) x acc =
  let trv = { exp; iter; iterexp; path; def } in
  let x', acc' = traverse x trv acc in
  (x', acc')