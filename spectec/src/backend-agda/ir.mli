type id = Id of string

type const =
  | SetC
  | BoolC
  | NatC
  | TextC
  | Bool of bool
  | Nat of int
  | Text of string

type pat =
  | VarP of id
  | ConstP of const
  | TupleP of pat list
  | YetP of string
  | CaseP of id * pat

type exp =
  | VarE of id
  | ConstE of const
  | ProdE of exp list
  | TupleE of exp list
  | ListE of exp
  | NilE
  | ConsE of exp * exp
  | MaybeE of exp
  | YetE of string
  | ArrowE of exp * exp
  | ApplyE of exp * exp
  | DotE of exp * id * id

type cons = id * (id * exp) list * exp list * exp
type field = id * exp
type clause = pat list * exp

type def =
  | DefD of id * exp * clause list
  | DataD of id * exp * cons list
  | RecordD of id * exp * field list
  | MutualD of def list

type program = def list