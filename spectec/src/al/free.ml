open Ast

let rec free_expr = function
  | NumE _
  | StringE _
  | GetCurLabelE
  | GetCurContextE
  | GetCurFrameE
  | YetE _ -> []
  | NameE n -> [n]
  | MinusE e
  | LengthE e
  | ArityE e
  | ContE e -> free_expr e
  | BinopE (_, e1, e2)
  | ListFillE (e1, e2)
  | ConcatE (e1, e2)
  | PairE (e1, e2)
  | ArrowE (e1, e2)
  | FrameE (e1, e2)
  | LabelE (e1, e2) -> free_expr e1 @ free_expr e2
  | AppE (_, es)
  | ListE es
  | ConstructE (_, _, es) -> List.concat_map free_expr es
  | RecordE _ -> (* TODO *) []
  | AccessE (e, p) -> free_expr e @ free_path p
  | ExtendE (e1, ps, e2, _)
  | ReplaceE (e1, ps, e2) -> free_expr e1 @ List.concat_map free_path ps @ free_expr e2
  | OptE e_opt -> List.concat_map free_expr (Option.to_list e_opt)
  | IterE (e, _, i) -> free_expr e @ free_iter i
and free_iter = function
  | Opt
  | List
  | List1 -> []
  | ListN (e, name_opt) -> Option.to_list name_opt @ free_expr e
and free_path _ = [] (* TODO *)