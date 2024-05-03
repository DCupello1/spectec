(*
This transformation removes uses of the `otherwise` (`ElsePr`) premise from
inductive relations.

It only supports binary relations.

1. It figures out which rules are meant by “otherwise”:

   * All previous rules
   * Excluding those that definitely can’t apply when the present rule applies
     (decided by a simple and conservative comparision of the LHS).

2. It creates an auxillary inductive unary predicate with these rules (LHS only).

3. It replaces the `ElsePr` with the negation of that rule.

*)

open Util
open Source
open Il.Ast

(* Brought from Apart.ml *)

(* Looks at an expression of type list from the back and chops off all
   known _elements_, followed by the list of all list expressions.
   Returns it all in reverse order.
 *)
 let rec to_snoc_list (e : exp) : exp list * exp list = match e.it with
 | ListE es -> List.rev es, []
 | CatE (e1, e2) ->
   let tailelems2, listelems2 = to_snoc_list e2 in
   if listelems2 = []
   (* Second list is fully known? Can look at first list *)
   then let tailelems1, listelems1 = to_snoc_list e1 in
        tailelems2 @ tailelems1, listelems1
   (* Second list has unknown elements, have to stop there *)
   else tailelems2, listelems2 @ [e1]
 | _ -> [], [e]

(* We assume the expressions to be of the same type; for ill-typed inputs
  no guarantees are made. *)
let rec apart (e1 : exp) (e2: exp) : bool =
 if Il.Eq.eq_exp e1 e2 then false else
 (*
 (fun b -> if not b then Printf.eprintf "apart\n  %s\n  %s\n  %b\n" (Print.string_of_exp e1) (Print.string_of_exp e2) b; b)
 *)
 (match e1.it, e2.it with
 (* A literal is never a literal of other type *)
 | NatE n1, NatE n2 -> not (n1 = n2)
 | BoolE b1, BoolE b2 -> not (b1 = b2)
 | TextE t1, TextE t2 -> not (t1 = t2)
 | CaseE (a1, exp1), CaseE (a2, exp2) ->
   not (a1 = a2) || apart exp1 exp2
 | TupE es1, TupE es2 when List.length es1 = List.length es2 ->
   List.exists2 apart es1 es2
 | (CatE _ | ListE _), (CatE _ | ListE _) ->
   list_exp_apart e1 e2
 | SubE (e1, _, _), SubE (e2, _, _) -> apart e1 e2
 (* We do not know anything about variables and functions *)
 | _ , _ -> false (* conservative *)
 )

(* Two list expressions are apart if either their manifest tail elements are apart *)
and list_exp_apart e1 e2 = snoc_list_apart (to_snoc_list e1) (to_snoc_list e2)

and snoc_list_apart (tailelems1, listelems1) (tailelems2, listelems2) =
 match tailelems1, listelems1, tailelems2, listelems2 with
 (* If the heads are apart, the lists are apart *)
 | e1 :: e1s, _, e2 :: e2s, _ -> apart e1 e2 || snoc_list_apart (e1s, listelems1) (e2s, listelems2)
 (* If one list is definitely empty and the other list definitely isn't *)
 | [], [], _ :: _, _ -> false
 | _ :: _, _, [], [] -> false
 (* Else, can't tell *)
 | _, _, _, _ -> false

(* Errors *)

let error at msg = Error.error at "else removal" msg

let empty_info: region * Il.Atom.info = (no_region, {def = ""; case = ""})
let unary_mixfix : mixop = [[Il.Atom.Atom "" $$ empty_info]; [Il.Atom.Atom "" $$ empty_info]]

let is_else prem = prem.it = ElsePr

let replace_else aux_name lhs prem = match prem.it with
  | ElsePr -> (RulePr (aux_name, unary_mixfix, lhs) $ prem.at)
  | _ -> prem

let unarize rule = match rule.it with 
    | RuleD (rid, binds, _mixop, exp, prems) ->
      let lhs = match exp.it with
        | TupE [lhs; _] -> lhs
        | _ -> error exp.at "expected manifest pair"
      in
      { rule with it = RuleD (rid, binds, unary_mixfix, lhs, prems) }

let not_apart lhs rule = match rule.it with
    | RuleD (_, _, _, lhs2, _) -> not (apart lhs lhs2)

let rec go at id mixop typ typ1 prev_rules : rule list -> def list = function
  | [] -> [ RelD (id, mixop, typ, List.rev prev_rules) $ at ]
  | r :: rules -> match r.it with
    | RuleD (rid, binds, rmixop, exp, prems) ->
      if List.exists is_else prems
      then
        let lhs = match exp.it with
          | TupE [lhs; _] -> lhs
          | _ -> error exp.at "expected manifest pair"
        in
        let aux_name = id.it ^ "_before_" ^ rid.it $ rid.at in
        let applicable_prev_rules = prev_rules
              |> List.map unarize
              |> List.filter (not_apart lhs)
              |> List.rev in
        [ RelD (aux_name, unary_mixfix, typ1, List.rev applicable_prev_rules) $ r.at ] @
        let prems' = List.map (replace_else aux_name lhs) prems in
        let rule' = { r with it = RuleD (rid, binds, rmixop, exp, prems') } in
        go at id mixop typ typ1 (rule' :: prev_rules) rules
      else
        go at id mixop typ typ1 (r :: prev_rules) rules

let rec t_def (def : def) : def list = match def.it with
  | RecD defs -> [ { def with it = RecD (List.concat_map t_def defs) } ]
  | RelD (id, mixop, typ, rules) -> begin match typ.it with
    | TupT [(_exp1, typ1); (_exp2, _typ2)] ->
      go def.at id mixop typ typ1 [] rules
    | _ -> [def]
    end
  | _ -> [ def ]

let transform (defs : script) =
  List.concat_map t_def defs