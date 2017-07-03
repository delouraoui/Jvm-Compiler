(** Conversion from Fopix to Anfix *)

(** For the moment, we only handle Fopix code which is already
    in ANF form (i.e. all arguments of function call and binop
    are simple). This is used for parsing Anfix without defining
    a full parser (but reusing Fopix parser instead) *)

module S = FopixAST
module T = AnfixAST

type environment = unit
let initial_environment () = ()
type defs = (T.identifier * T.expression) list
                                          
                                          
let fresh_variable =
  let r = ref 0 in
  fun f ->
  incr r;
  ("_x" ^ string_of_int !r)
    
let rec is_simple  = function
  | S.Num n -> true
  | S.FunName f -> true
  | S.Var x -> true
  | _ -> false
           
let rec is_simple'  = function
  | T.E (T.Num n) -> true
  | T.E (T.FunName f) -> true
  | T.E (T.Var x) -> true
  | _ -> false
           
let subst_simpl x u = function
  | T.Num n -> (T.Num n)
  | T.Var x' when (x = x')  -> u 
  | T.FunName f when  f = x -> u
  | _ -> assert false 
               
(* let rec subst x u = *)
(*   function  *)
(*   | T.E (T.Def (id,e1,e2,())) -> *)
(*      let T.E e1 = subst x u (T.E e1) in *)
(*      let T.E e2 = subst x u (T.E e2) in *)
(*      T.E (T.Def (id,e1,e2,())) *)
         
(*   | T.E (T.IfThenElse (cond,tbranch,fbranch)) -> *)
(*      let T.E tbranch = subst x u (T.E tbranch) in *)
(*      let T.E fbranch = subst x u (T.E fbranch) in *)
(*      T.E (T.IfThenElse (cond,tbranch,fbranch)) *)
         
(*   | T.E (T.BinOp (op,e1,e2)) -> *)
(*     let e1 = subst_simpl x u e1 in *)
(*     let e2 = subst_simpl x u e2 in *)
(*     T.E (T.BinOp (op,e1,e2)) *)
        
(*   | T.E (T.BlockNew array) -> *)
(*      let array = subst_simpl x u array in *)
(*      T.E (T.BlockNew array) *)
         
(*   | T.E (T.BlockGet (array,index)) -> *)
(*      let array = subst_simpl x u array in *)
(*      let index = subst_simpl x u index in *)
(*      T.E (T.BlockGet (array,index)) *)
         
(*   | T.E (T.BlockSet (array,index,value)) -> *)
(*      let array = subst_simpl x u array in *)
(*      let index = subst_simpl x u index in *)
(*      let value = subst_simpl x u value in *)
(*      T.E (T.BlockSet (array,index,value)) *)
         
(*   | T.E (T.FunCall  (fexpr,args)) -> *)
(*      let fexpr = subst_simpl x u fexpr in *)
(*      let args = List.map (fun e -> *)
(*                     let e = subst_simpl x u e in e *)
(*                   ) args in *)
(*      T.E (T.FunCall  (fexpr,args)) *)
         
(*   | T.E (T.Var x') when x = x  -> T.E u *)
(*   | T.E T.Num n -> T.E (T.Num n) *)
(*   | T.E T.Var x' when (x = x')   -> T.E u  *)
(*   | T.E T.FunName f when  f = x  ->  T.E u                    *)
(*   | e -> e *)
           
let rec check = function  
  | S.Def (x,e1,e2)  ->
     (check e1) && check e2
         
  | S.IfThenElse (e1,e2,e3) ->
     is_simple e1 && check e2 && check e3
     
  | S.BinOp (b,e1,e2) ->
     is_simple e1 && is_simple e2
                
  | S.BlockNew e ->
     true
                      
  | S.BlockGet (e1,e2) ->
     is_simple e1 && is_simple e2

  | S.BlockSet (e1,e2,e3) ->
     true       
                               
  | S.FunCall (e,el) ->
     is_simple e && (List.for_all (fun x -> is_simple x) el)

  | _ -> true

(* let rec fv : type kind. *)
(*   T.identifier list -> (kind,_) T.expr -> T.identifier list *)
(*   = fun acc e -> match e with *)
(*     | T.Def (id,e1,e2,()) -> *)
(*     fv acc e1 @ fv (id :: acc) e2 *)
(*   | T.IfThenElse (cond,tbranch,fbranch) -> *)
(*     fv acc cond @ fv acc tbranch @ fv acc fbranch *)
(*   | T.BinOp (op,e1,e2) -> *)
(*     fv acc e1 @ fv acc e2 *)
(*   | T.BlockNew array -> fv acc array *)
(*   | T.BlockGet (array,index) -> *)
(*     fv acc array @ fv acc index *)
(*   | T.BlockSet (array,index,value) -> *)
(*     fv acc array @ fv acc index @ fv acc value *)
(*   | T.FunCall  (fexpr,args) -> *)
(*     fv acc fexpr @ List.flatten (List.map (fun x -> fv acc x) args) *)
(*   | T.Var x when not (List.mem x acc)-> [x] (\* fixme *\) *)
(*   | _ -> [] *)

let collect_def e = 
  let rec collect_def acc = function
    | [] -> List.rev acc
    | T.DefVal (i,T.E e)::q (* when (is_simple' (T.E e)) *) ->
       collect_def ((i,(T.E e))::acc) q
       (* begin *)
       (*   match e with *)
       (*   | T.Num n -> collect_def ((i,(T.Num n))::acc) q *)
       (*   | T.Var x ->collect_def ((i,T.Var x)::acc) q *)
       (*   | T.FunName f -> collect_def ((i,T.FunName f)::acc) q *)
       (*   | _ -> failwith "we can't transforme programme of the form :\n *)
       (*                    val x = complex_expression val y = ... may be with *)
       (*                    some trick you can transforme it :) " *)
       (* end *)
    | a::q ->
       collect_def acc q in
  collect_def [] e
                 
let rec build_local_pg = function
  | [] -> assert false (** never happend **) 
  | [(i,a)] ->  a
  | (i,T.E e1) :: q ->
     let T.E e1 = T.E e1 in 
     let T.E e2 = build_local_pg q in
     T.E (T.Def(i,e1,e2,()))
         
let rec collect_fun = function
  | [] -> []
  | T.DefFun (f,a,T.E e)::q ->
    (T.DefFun (f,a,T.E e))::collect_fun q
  | e::q -> collect_fun q

         
(* let rec instanciate_fun substlst = function *)
(*   | [] -> [] *)
(*   | T.DefFun (f,a,T.E e)::q -> *)
(*      let fv_e = fv (f::a) e in  *)
(*      let T.E e = *)
(*        List.fold_left (fun acc x -> *)
(*            try  *)
(*              let u = List.assoc x substlst in *)
(*              subst x u acc *)
(*            with e -> acc) (T.E e) fv_e in *)
(*     (T.DefFun (f,a,T.E e))::instanciate_fun substlst q *)
(*   | e::q -> instanciate_fun substlst q *)
                            
let make_local_form p =
  let substlst = collect_def p in  
    if List.length substlst > 0 then begin  
        let prog_in_localfm =  build_local_pg substlst in
        let fun_def = collect_fun p in
        (* let fun_reduced = instanciate_fun substlst p in *)
        
        fun_def@[T.DefVal ("_main_",prog_in_localfm)] end
    else p
                              
let rec program l =
  let prog = List.map definition l in
  (** On construit on compact les définitions en une seule définition
      local exemple :
       val x = 1 val y = 3 val j = x + y ==> 
       val res = 
       val x = 1 in
       val y = 3 in 
       x + y
     On prend nottament en compte les cas ou x apparait libre dans le 
     corps d'une fonction déclaré plus bas : 
       val x = 1 val y = 3 def f(x) = x + y 
     Ou ici x est local à f mais y est libre dans f est a pour valeur 3
    **)
  make_local_form prog
           
and definition = function
  | S.DefVal (i,e) ->
     if check e then
       T.DefVal (i,identity e)
     else
       T.DefVal (i,expr e)
  | S.DefFun (f,a,e) ->
     if check e then
       T.DefFun (f,a,identity e)
     else
       T.DefFun (f,a,expr e)

and simplexpr : S.expression -> (T.simple,unit) T.expr =
  function
  | S.Num n -> T.Num n
  | S.FunName f -> T.FunName f
  | S.Var x -> T.Var x
  | e -> failwith ("This expression should be simple:" ^
                     FopixPrettyPrinter.(to_string expression e))
     
and build_art3 e1 e2 e3 constructor =
  let idcond = fresh_variable () in
   let right  =
     expr e3 in
  let left   =
    expr e2 in
  let left = left in
  let right  = right in
  if not(is_simple e1) then begin
      let T.E(e1') = expr e1  in
      T.E (T.Def(idcond,e1',constructor (T.Var idcond) left right, () ))
    end
  else 
    T.E (constructor (simplexpr e1) left right)
         
and build_art2 e1 e2 constructor = 
  let id1 = fresh_variable () in
  let id2 = fresh_variable () in
   if not(is_simple e1) then begin
      if not(is_simple e2) then
        begin
          let T.E(e1') = expr e1  in
          let T.E(e2') = expr e2  in
          let bottom =
            (T.Def(id2,e2', constructor (T.Var id1) (T.Var id2) , () )) in 
          T.E (T.Def(id1,e1', bottom, () ))
        end else begin
          let T.E(e1') = expr e1  in
          let e2' = simplexpr e2  in
          T.E (T.Def(id1,e1',constructor (T.Var id1) e2', ())) end
    end
  else if not(is_simple e2) then
    begin
      let e1' = simplexpr e1  in
      let T.E(e2') = expr e2  in
      T.E (T.Def(id2,e2', constructor e1' (T.Var id2), () ))
    end 
  else begin 
      let e1' = simplexpr e1  in
      let e2' = simplexpr e2  in
      T.E (constructor e1' e2') end
         
and expr : S.expression -> T.expression = function
  | S.Num n -> T.E (T.Num n)
  | S.FunName f -> T.E (T.FunName f)
  | S.Var x -> T.E (T.Var x)
  | S.Def (x,e1,e2) ->
     let T.E e1' = expr e1  in
     let T.E e2' = expr e2  in
     T.E (T.Def(x,e1', e2',()))
         
  | S.IfThenElse (e1,e2,e3) ->
     build_art3 e1 e2 e3 (fun e1 e2 e3 ->
                  let T.E e2 = e2 in
                  let T.E e3 = e3 in
                  T.IfThenElse(e1, e2, e3))
         
  | S.BinOp (b,e1,e2) ->
     build_art2 e1 e2 (fun e1 e2 -> T.BinOp (b, e1 ,e2))
                
  | S.BlockNew e ->
     let se = simplexpr e in  T.E (T.BlockNew se)
                                  
  | S.BlockGet (e1,e2) ->
     build_art2 e1 e2 (fun e1 e2 -> T.BlockGet (e1 ,e2))

  | S.BlockSet (e1,e2,e3) ->
     let se1 = simplexpr e1 in
     let se2 = simplexpr e2 in
     let se3 = simplexpr e3 in   
     T.E (T.BlockSet (se1,se2,se3))
         
  | S.FunCall (e,el) ->
     let se = simplexpr e in
     let el,look =
       List.fold_right
         (fun x (acc,env) ->
           match x with
           | S.FunCall (e,el) ->
              let id = fresh_variable () in
              let look = (T.Var id)::env in
              let T.E(e') = expr (S.FunCall (e,el)) in
              let T.E e1 =  acc in
              T.E (T.Def(id,e', e1, () )),look                                    
           | e when not(is_simple e)   ->
              let id = fresh_variable () in
              let look =  (T.Var id)::env in
              let T.E e1 =  acc in
              let T.E(e') = expr e in
              T.E (T.Def(id,e', e1, ())),look
           | e -> acc,(simplexpr e)::env
         ) el ((T.E (T.FunCall (se,[]))),[]) in
     let retour =
       let rec traverse =
         begin
           function
           | T.E (T.Def(id,e,  e1, ())) ->
              let T.E e1' =  traverse (T.E e1) in
              T.E (T.Def(id, e,e1', ()))

           | T.E (T.FunCall (se,[])) ->
              T.E (T.FunCall (se,look))
           | e -> e
         end in traverse el in retour

                  
and identity : S.expression -> T.expression = function
  | S.Num n -> T.E (T.Num n)
  | S.FunName f -> T.E (T.FunName f)
  | S.Var x -> T.E (T.Var x)
  | S.Def (x,e1,e2) ->
     let T.E e1 = identity e1 in
     let T.E e2 = identity e2 in
     T.E (T.Def (x, e1 ,e2,()))
         
  | S.IfThenElse (e1,e2,e3) ->
     let e1 = simplexpr e1 in
     let T.E e2 = identity e2 in
     let T.E e3 = identity e3 in
     T.E (T.IfThenElse(e1, e2, e3))
         
  | S.BinOp (b,e1,e2) ->
     T.E (T.BinOp (b, simplexpr e1 ,simplexpr e2))
                
  | S.BlockNew e ->  
     T.E (T.BlockNew (simplexpr e))
         
  | S.BlockGet (e1,e2) ->
     T.E (T.BlockGet (simplexpr e1 ,simplexpr e2))

  | S.BlockSet (e1,e2,e3) ->
     T.E (T.BlockSet (simplexpr e1 ,simplexpr e2,simplexpr e3 ))
         
  | S.FunCall (e,el) ->
     T.E (T.FunCall(simplexpr e,List.map simplexpr  el))
