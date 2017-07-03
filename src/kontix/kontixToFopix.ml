(** Conversion from Kontix to a subset of Fopix *)

(** This is used for instance during evaluation *)

module S=KontixAST
module T=FopixAST

let fresh_id =
  let r = ref (-1) in
  fun s -> incr r; s^(string_of_int !r)

let rec program (l,e) =
  List.map definition l @
  [T.DefFun ("_return_",["x";"E"],T.Var "x");
   T.DefVal ("res",tailexpr ~main:true e)]

and definition = function
  | S.DefFun (f,a,e) -> T.DefFun (f,"K"::"E"::a,tailexpr e)
  | S.DefCont (f,x,ids,e) ->
     let id = fresh_id "__env" in
     T.DefFun (f,[x;id],untuple (T.Var id) 0 ("K"::"E"::ids) (tailexpr e))

and untuple ptr i ids e = match ids with
  | [] -> e
  | id::ids -> T.Def (id,T.BlockGet (ptr,T.Num i),
                      untuple ptr (i+1) ids e)

and tailexpr ?(main=false) = function
  | S.TDef (x,e1,e2) -> T.Def (x, basicexpr e1, tailexpr ~main e2)
  | S.TIfThenElse (e1,e2,e3) ->
     T.IfThenElse (basicexpr e1, tailexpr ~main e2, tailexpr ~main e3)
  | S.TFunCall (e,el,kenv) ->
     T.FunCall (basicexpr e, kont_env main kenv @ List.map basicexpr el)
  | S.TContCall (kenv,e) ->
     (match kont_env main kenv with
      | [hd;env] -> T.FunCall (hd, [basicexpr e; env])
      | _ -> assert false)

and basicexpr = function
  | S.Num n -> T.Num n
  | S.FunName f -> T.FunName f
  | S.Var x -> T.Var x
  | S.Def (x,e1,e2) -> T.Def (x,basicexpr e1, basicexpr e2)
  | S.IfThenElse (e1,e2,e3) ->
     T.IfThenElse (basicexpr e1, basicexpr e2, basicexpr e3)
  | S.BinOp (o,e1,e2) -> T.BinOp (o, basicexpr e1, basicexpr e2)
  | S.BlockNew e -> T.BlockNew (basicexpr e)
  | S.BlockGet (e1,e2) -> T.BlockGet (basicexpr e1, basicexpr e2)
  | S.BlockSet (e1,e2,e3) ->
     T.BlockSet (basicexpr e1, basicexpr e2, basicexpr e3)

and kont_env main = function
  | S.CurCont when main -> [T.FunName "_return_"; T.BlockNew (T.Num 0)]
  | S.CurCont -> [T.Var "K";T.Var "E"]
  | S.PushCont (f,kenv,ids) ->
     let id = fresh_id "__blk" in
     let l = kont_env main kenv @
             List.map (fun id -> T.Var id) ids in
     [T.FunName f;
      T.Def (id,T.BlockNew (T.Num (2+List.length ids)),
            settuple (T.Var id) 0 l (T.Var id))]

and settuple e0 i el e = match el with
  | [] -> e
  | ei::el -> T.Def ("_",T.BlockSet(e0,T.Num i,ei),
                     settuple e0 (i+1) el e)
