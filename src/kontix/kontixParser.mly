%{

open KontixAST

type expr_or_tuple =
  | Expr of basicexpr
  | Kont
  | Env
  | Tuple of expr_or_tuple list

let rec mkcont k e =
  match k,e with
  | Kont, Env -> CurCont
  | Expr(FunName f), Tuple (k::e::ids) when
         List.for_all (function Expr (Var _) -> true | _ -> false) ids
    ->
     let ids = List.map (function Expr (Var id) -> id | _ -> "") ids in
     PushCont (f, mkcont k e, ids)
  | _ -> raise Not_found

let mkcall f l startpos endpos =
  match f, l with
  | None, [Expr res; Env] -> TContCall (CurCont, res)
  | Some (FunName f), [Expr res; Tuple l] ->
     (try
         TContCall (mkcont (Expr (FunName f)) (Tuple l), res)
      with Not_found ->
        let pos = Position.lex_join startpos endpos in
        Error.error "parsing" pos
                    "bad application to a continuation")
  | Some e, (k::env::args) ->
     (try
         let a = List.map (function Expr e -> e | _ -> raise Not_found) args in
         TFunCall (e, a, mkcont k env)
       with Not_found ->
         let pos = Position.lex_join startpos endpos in
         Error.error "parsing" pos
         "bad application (missing or badly shaped arguments)")
  | _ ->
     let pos = Position.lex_join startpos endpos in
     Error.error "parsing" pos
     "bad application (missing or badly shaped arguments)"

%}

%token VAL DEF IN END IF THEN ELSE EVAL UPPERSAND QMARK NEW K E
%token PLUS MINUS STAR SLASH GT GTE LT LTE EQUAL PERCENT
%token LPAREN RPAREN LBRACKET RBRACKET ASSIGNS COMMA SEMICOLON EOF
%token<int> INT
%token<string> ID

%right SEMICOLON
%nonassoc ASSIGNS
%nonassoc GT GTE LT LTE EQUAL
%left PLUS MINUS
%left STAR SLASH PERCENT
%nonassoc LBRACKET

%start<KontixAST.t> program

%%

program: ds=definition* EVAL e=expression EOF
{
  ds,e
}
| error {
  let pos = Position.lex_join $startpos $endpos in
  Error.error "parsing" pos "Syntax error."
}

definition:
  DEF f=function_identifier
  LPAREN res=identifier COMMA ids=tuple RPAREN
  EQUAL e=expression
{
  DefCont (f,res,ids,e)
}
| DEF f=function_identifier
  LPAREN K COMMA E ids=list(preceded(COMMA,identifier)) RPAREN
  EQUAL e=expression
{
  DefFun (f,ids,e)
}

tuple:
 LBRACKET K COMMA E ids=list(preceded(COMMA,identifier)) RBRACKET
 { ids }

basic_expression:
  x=INT { Num x }
| UPPERSAND f=function_identifier { FunName f }
| x=identifier { Var x }
| VAL x=identifier EQUAL
    e1=basic_expression
  IN
    e2=basic_expression
  END
{
  Def (x, e1, e2)
}
| IF
  c=basic_expression
  THEN t=basic_expression
  ELSE f=basic_expression
  END
{
  IfThenElse (c, t, f)
}
| l=basic_expression b=binop r=basic_expression {
  BinOp (b, l, r)
}
| e=basic_expression LBRACKET i=basic_expression RBRACKET {
  BlockGet (e, i)
}
| e=basic_expression
  LBRACKET i=basic_expression RBRACKET
  ASSIGNS v=basic_expression {
  BlockSet (e, i, v)
}
| NEW LBRACKET e=basic_expression RBRACKET {
  BlockNew (e)
}

| e1=basic_expression SEMICOLON e2=basic_expression {
  Def ("_", e1, e2)
}
| LPAREN e=basic_expression RPAREN {
  e
}

expression:
| VAL x=identifier
  EQUAL
    e1=basic_expression
  IN
    e2=expression
  END
{
  TDef (x, e1, e2)
}
| e1=basic_expression SEMICOLON e2=expression {
  TDef ("_", e1, e2)
}
| IF
  c=basic_expression
  THEN t=expression
  ELSE f=expression
  END
{
  TIfThenElse (c, t, f)
}
| f=fun_head
  LPAREN l=separated_list(COMMA,basicexpr_or_tuple) RPAREN
{
  mkcall f l $startpos $endpos
}

fun_head:
| QMARK LPAREN e=basic_expression RPAREN { Some e }
| f=function_identifier { Some (FunName f) }
| K { None }

basicexpr_or_tuple:
LBRACKET es=separated_list(COMMA, basicexpr_or_tuple) RBRACKET
 { Tuple es }
| e=basic_expression { Expr e }
| K { Kont }
| E { Env }

%inline binop:
  PLUS  { Add }
| MINUS { Sub }
| STAR  { Mul }
| SLASH { Div }
| PERCENT { Mod }
| GT    { Gt }
| GTE   { Ge }
| LT    { Lt }
| LTE   { Le }
| EQUAL { Eq }

%inline identifier: x=ID {
  x
}

%inline function_identifier: x=ID {
  x
}
