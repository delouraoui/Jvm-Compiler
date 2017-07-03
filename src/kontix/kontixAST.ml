(** The abstract syntax tree for kontix programs. *)

type program = definition list * tailexpr
(** this tailexpr serves as a main.
    In it, [CurCont] means the initial continuation _return_
    and the empty environment *)

and definition =
  | DefFun of function_identifier * formals * tailexpr
  (** def fun_name () **)
  | DefCont of function_identifier * identifier * formal_env * tailexpr

and basicexpr =
  | Num of int
  | FunName of function_identifier
  | Var of identifier
  | Def of identifier * basicexpr * basicexpr
  | IfThenElse of basicexpr * basicexpr * basicexpr
  | BinOp of binop * basicexpr * basicexpr
  | BlockNew of basicexpr
  | BlockGet of basicexpr * basicexpr
  | BlockSet of basicexpr * basicexpr * basicexpr

and tailexpr =
  | TDef of identifier * basicexpr * tailexpr
  | TIfThenElse of basicexpr * tailexpr * tailexpr
  | TFunCall of basicexpr * basicexpr list * continuation_and_env
  | TContCall of continuation_and_env * basicexpr
                                           
(* Call a continuation with its environment and a result *)
and identifier = string
and function_identifier = string

and formals = identifier list

 (* Standard arg names. *)
 (* Continuation and env aren't mentionned here, *)
 (* since they are nameless now. *)

and formal_env = identifier list

(* saved variables names. *)
(* (and implicitely a inner continuation and env) *)

and continuation_and_env =
  | CurCont (* Current continuation and environment *)
  | PushCont of function_identifier * continuation_and_env * identifier list

(* Use this name as continuation, *)
(* and make a new environment that stores *)
(* the previous continuation and environment, and *)
(* the content of the mentionned variables *)

and binop = FopixAST.binop =
  | Add | Sub | Mul | Div | Mod (* arithmetic ops *)
  | Eq | Le | Lt | Ge | Gt (* comparisons *)

and t = program
