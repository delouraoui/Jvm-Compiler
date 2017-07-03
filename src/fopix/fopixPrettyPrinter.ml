open PPrint
open PPrintCombinators
open PPrintEngine

open FopixAST

let ( ++ ) x y =
  x ^^ break 1 ^^ y

let located f x = f (Position.value x)

let rec program p =
  separate_map hardline definition p

and definition = function
  | DefVal (x, e) ->
    nest 2 (
      group (string "val" ++ identifier x ++ string "=")
      ++ group (expression e)
    )

  | DefFun (f, xs, e) ->
    nest 2 (
      group (string "def" ++ function_identifier f
             ++ PPrintOCaml.tuple (List.map identifier xs)
             ++ string "=")
      ++ group (expression e)
    )

and identifier x = string x

and function_identifier x = string x

and expression = function
  | Num n -> string (string_of_int n)
  | FunName f -> string ("&" ^ f)
  | Var v -> string v
  | IfThenElse (c, t, f) ->
    nest 2 (
      group (string "if"
             ++ group (expression c)
             ++ string "then"
      )
      ++ group (expression t)
      ++ string "else"
      ++ group (expression f)
    )
    ++ string "end"
  | Def (x, e1, e2) ->
    nest 2 (
      group (
        group (string "val"
               ++ identifier x
               ++ string "="
        )
        ++ group (expression e1)
        ++ string "in"
      )
    )
    ++ group (expression e2)
    ++ string "end"
  | FunCall (FunName f, es) ->
     string f ++ PPrintOCaml.tuple (List.map expression es)
  | FunCall (e, es) ->
    string "?" ++ parens (expression e)
    ++ PPrintOCaml.tuple (List.map expression es)
  | BlockNew e ->
     string "new" ++ brackets (expression e)
  | BlockGet (e1,e2) ->
     group (expression e1) ++ brackets (expression e2)
  | BlockSet (e1,e2,e3) ->
     group (expression e1) ++ brackets (expression e2) ++
     string ":=" ++ group (expression e3)
  | BinOp (op,e1,e2) ->
     group (parens (expression e1 ++ string (binop op) ++ expression e2))

and binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Eq -> "="
  | Le -> "<="
  | Ge -> ">="
  | Lt -> "<"
  | Gt -> ">"

let to_string f x =
  let b = Buffer.create 13 in
  ToBuffer.pretty 0.5 80 b (f x);
  Buffer.contents b
