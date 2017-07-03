(** The abstract syntax tree for fopix programs. *)

type program = definition list

and definition =
  | DefVal of identifier * expression
  | DefFun of function_identifier * formals * expression

and expression =
  | Num of int
  | FunName of function_identifier
  | Var of identifier
  | Def of identifier * expression * expression
  | IfThenElse of expression * expression * expression
  | BinOp of binop * expression * expression
  | BlockNew of expression                           (* size *)
  | BlockGet of expression * expression              (* array, index *)
  | BlockSet of expression * expression * expression (* array, index, value *)
  | FunCall of expression * expression list

and identifier = string

and formals = identifier list

and function_identifier = string

and binop =
  | Add | Sub | Mul | Div | Mod (* arithmetic ops *)
  | Eq | Le | Lt | Ge | Gt (* comparisons *)

and t = program
