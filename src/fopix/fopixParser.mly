%{

  open FopixAST

%}

%token VAL DEF IN END IF THEN ELSE EVAL UPPERSAND QMARK NEW
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

%start<FopixAST.t> program

%%

program: ds=definition* EOF
{
  ds
}
| error {
  let pos = Position.lex_join $startpos $endpos in
  Error.error "parsing" pos "Syntax error."
}

definition: VAL x=located(identifier) EQUAL e=located(expression)
{
  DefVal (x, e)
}
| DEF f=located(function_identifier)
  LPAREN xs=separated_list(COMMA, identifier) RPAREN
  EQUAL e=located(expression)
{
  DefFun (f, xs, e)
}
| EVAL e=located(expression)
{
  DefVal ("_", e)
}

expression:
  x=INT
{
  Num x
}
| UPPERSAND f=function_identifier
{
  FunName f
}
| x=identifier
{
  Var x
}
| VAL x=located(identifier)
  EQUAL
    e1=located(expression)
  IN
    e2=located(expression)
  END
{
  Def (x, e1, e2)
}
| IF
  c=located(expression)
  THEN t=located(expression)
  ELSE f=located(expression)
  END
{
  IfThenElse (c, t, f)
}
| QMARK LPAREN e=located(expression) RPAREN
  LPAREN es=separated_list(COMMA, located(expression)) RPAREN
{
  FunCall (e, es)
}
| f=function_identifier
  LPAREN es=separated_list(COMMA, located(expression)) RPAREN
{
  FunCall (FunName f, es)
}
| l=located(expression) b=binop r=located(expression) {
  BinOp (b, l, r)
}
| e=located(expression) LBRACKET i=located(expression) RBRACKET {
  BlockGet (e, i)
}
| e=located(expression)
  LBRACKET i=located(expression) RBRACKET
  ASSIGNS v=located(expression) {
  BlockSet (e, i, v)
}
| NEW LBRACKET e=located(expression) RBRACKET {
  BlockNew e
}

| e1=located(expression) SEMICOLON e2=located(expression) {
  Def ("_", e1, e2)
}
| LPAREN e=expression RPAREN {
  e
}

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

%inline located(X): x=X {
  (*Position.with_poss $startpos $endpos*) x
}
