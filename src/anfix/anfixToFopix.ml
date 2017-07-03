(** Conversion from Anfix to a subset of Fopix *)

(** This is used for instance during printing *)

module S = AnfixAST
module T = FopixAST

let rec program l = List.map definition l

and definition = function
  | S.DefVal (i,S.E e) -> T.DefVal (i, expr e)
  | S.DefFun (f,a,S.E e) -> T.DefFun (f,a, expr e)

and expr : type a. (a,unit) S.expr -> T.expression = function
  | S.Num n -> T.Num n
  | S.FunName f -> T.FunName f
  | S.Var x -> T.Var x
  | S.Def (x,e1,e2,()) -> T.Def (x,expr e1,expr e2)
  | S.IfThenElse (e1,e2,e3) -> T.IfThenElse (expr e1,expr e2,expr e3)
  | S.BinOp (b,e1,e2) -> T.BinOp (b,expr e1,expr e2)
  | S.BlockNew e -> T.BlockNew (expr e)
  | S.BlockGet (e1,e2) -> T.BlockGet (expr e1,expr e2)
  | S.BlockSet (e1,e2,e3) -> T.BlockSet (expr e1,expr e2,expr e3)
  | S.FunCall (e,el) -> T.FunCall (expr e, List.map expr el)
