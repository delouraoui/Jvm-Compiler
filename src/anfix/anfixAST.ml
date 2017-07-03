(** The abstract syntax tree for anfix programs. *)

(** Anfix is the same as Fopix, except that:
    - function call arguments must be "simple" (variables or consts)
    - same for "if" conditions and primitive arguments
*)

type simple = Simple
type complex = Complex

type program = definition list

and definition =
  | DefVal of identifier * expression
  | DefFun of function_identifier * formals * expression

and expression =
  | E : ('any,unit) expr -> expression
  (* 'any is an existential type parameter, cf GADT
      unit means no attribute annotation by default *)

(* first type parameter : simplicity of the expression
   snd type parameter : optional annotation attached to Def.
    (unit by default, will be enriched later). *)

and ('s,'a) expr =
  | Num : int -> (simple,'a) expr
  | FunName : function_identifier -> (simple,'a) expr
  | Var : identifier -> (simple,'a) expr
  | Def : identifier * (_,'a) expr * (_,'a) expr * 'a -> (complex,'a) expr
  | IfThenElse : (simple,'a) expr * (_,'a) expr * (_,'a) expr ->
    (complex,'a) expr
  | BinOp : binop * (simple,'a) expr * (simple,'a) expr -> (complex,'a) expr
  | BlockNew : (simple,'a) expr -> (complex,'a) expr
  | BlockGet : (simple,'a) expr * (simple,'a) expr -> (complex,'a) expr
  | BlockSet : (simple,'a) expr * (simple,'a) expr * (simple,'a) expr ->
    (complex,'a) expr
  | FunCall : (simple,'a) expr * (simple,'a) expr list -> (complex,'a) expr

and identifier = string

and formals = identifier list

and function_identifier = string

and binop = FopixAST.binop =
  | Add | Sub | Mul | Div | Mod (* arithmetic ops *)
  | Eq | Le | Lt | Ge | Gt (* comparisons *)

and t = program
