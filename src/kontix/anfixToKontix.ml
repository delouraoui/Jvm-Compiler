(** This module implements a compiler from Anfix to Kontix. *)

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)
module Source = Anfix
module Target = Kontix

module S = Source.AST
module T = Target.AST

open T

let fresh_id =
  let r = ref (-1) in
  fun s -> incr r; s ^ string_of_int !r

let rec drop_last = function
  | [] -> raise (Failure "drop_last")
  | [a] -> []
  | a::tl -> a:: drop_last tl

let ( >>= ) xs f = List.fold_right (fun x acc -> f x @ acc) xs []

type environment = unit (* TODO *)

let initial_environment () = () (* TODO *)

let rec is_simple : type kind. (kind,unit) S.expr -> bool = function
  | S.Def (id,e1,e2,()) ->
    is_simple e1  && is_simple e2
  | S.IfThenElse (cond,tbranch,fbranch) ->
    is_simple cond && is_simple tbranch && is_simple fbranch
  | S.BinOp (op,e1,e2) ->
    is_simple e1 && is_simple e2
  | S.BlockNew array ->
    is_simple array
  | S.BlockGet (array,index) ->
    is_simple array && is_simple index
  | S.BlockSet (array,index,value) ->
    is_simple array && is_simple index && is_simple value
  | S.FunCall (fexpr,args) ->false
  | _ -> true

let rec fv : type k. _ -> (k,_) S.expr -> _ = fun acc -> function
  | S.Def (id,e1,e2,()) ->
    fv acc e1 @ fv (id :: acc) e2
  | S.IfThenElse (cond,tbranch,fbranch) ->
    fv acc cond @ fv acc tbranch @ fv acc fbranch
  | S.BinOp (op,e1,e2) ->
    fv acc e1 @ fv acc e2
  | S.BlockNew array -> fv acc array
  | S.BlockGet (array,index) ->
    fv acc array @ fv acc index
  | S.BlockSet (array,index,value) ->
    fv acc array @ fv acc index @ fv acc value
  | S.FunCall  (fexpr,args) ->
    fv acc fexpr @ List.flatten (List.map (fun x -> fv acc x) args)
  | S.Var x when not (List.mem x acc)-> [x]
  | _ -> []                     (* fixme ? *)

let undress_def = function
  | DefCont (fun_id,id,frml,e) -> e
  | _ -> assert false

let is_def = function
  | DefCont (_,_,_,_) -> true
  | _ -> false

let rec program (p : S.t) =
  let defs = p >>= definition in
  let last_def = List.nth defs (List.length defs - 1 ) in
  if is_def last_def then
    (drop_last defs, undress_def last_def)
  else
    (defs, TContCall (CurCont,Num 0))

and definition = function
  | S.DefVal (id,S.E e) ->
    let kid = fresh_id "kontN" in
    let (toplvl,trans_term) = expression (S.E e) in
    toplvl @ [DefCont (kid,id, fv [id] e, trans_term)]
  | S.DefFun (f_id,formals,e) ->
    let (toplvl,trans_term) = expression e in
    toplvl @ [DefFun (f_id, formals, trans_term)]

and expression (S.E exp) = expr CurCont exp

and expr : type k. _ -> (k,_) S.expr -> _ = fun env -> function

  | S.Def (id,e1,e2,()) when is_simple e1 ->
    let (toplvl2,trans_term2) = expr env e2 in
    (toplvl2, TDef (id, coerce e1, trans_term2))

  | S.Def (id,e1,e2,()) ->
    let kid = fresh_id "kontN" in
    let fv_e2 = fv [id] e2 in
    let (toplvl1,trans_term1) = expr (PushCont (kid,env,fv_e2)) e1 in
    let (toplvl2,trans_term2) = expr CurCont e2 in
    let defs = toplvl2 @ toplvl1 @ [DefCont (kid,id,fv_e2,trans_term2)] in
    (defs,trans_term1)

  | S.IfThenElse (cond,tbranch,fbranch) ->
    let toplvl1,trans_tbranch  = expr env tbranch in
    let toplvl2,trans_fbranch  = expr env fbranch in
    let toplvl = toplvl2 @ toplvl1 in
    (toplvl, TIfThenElse (coerce cond, trans_tbranch, trans_fbranch))

  | S.FunCall  (fexpr,args) ->
    ([], TFunCall (coerce fexpr, List.map coerce args, env))

  | e ->
    ([], TContCall (env, coerce e))

and coerce : type k. (k, unit) S.expr -> basicexpr = function
  | S.Num const ->
    Num const
  | S.FunName f ->
    FunName f
  | S.Var id ->
    Var id
  | S.Def (id,e1,e2,()) ->
    Def (id,coerce e1, coerce e2)
  | S.IfThenElse (cond,tbranch,fbranch) ->
    IfThenElse (coerce cond, coerce tbranch, coerce fbranch)
  | S.BinOp (op,e1,e2) ->
    BinOp (op,coerce e1, coerce e2)
  | S.BlockNew (array) ->
    BlockNew (coerce  array)
  | S.BlockGet (array,index) ->
    BlockGet(coerce array, coerce index)
  | S.BlockSet (array,index,value) ->
    BlockSet (coerce  array, coerce  index, coerce value)
  | S.FunCall (fexpr,args) ->
    failwith "this should be simple expression"

let rec translate (p : S.t) env = (program p, env)
