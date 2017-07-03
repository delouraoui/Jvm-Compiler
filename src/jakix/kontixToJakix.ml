(** This module implements a compiler from Kontix to Fopix. *)

module List = struct

  include List

  let init n f =
    if n <= 0 then []
    else
      let rec loop n acc =
        if n = 0 then f 0 :: acc
        else loop (pred n) (f n :: acc)
      in loop (pred n) []

  let bind m f = fold_right (fun x acc -> f x @ acc) m []

  let assoc ?(fexn = fun _ -> Not_found) k xs =
    try assoc k xs
    with _ -> raise (fexn k)

  module Infix = struct
    let ( >|= ) m f = map f m
    let ( >>= ) m f = bind m f
  end

end

open List.Infix

let error pos msg =
  Error.error "compilation" pos msg


(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)

module Source = Kontix
module Target = Jakix

module S = Source.AST
module T = Target.AST

open T

(** We will need the following pieces of information to be carrying
    along the translation: *)
type environment = FopixToJavix.environment = {
  next_var         : int;
  variables        : (S.identifier * T.var) list;
  function_labels  : (S.function_identifier * T.label) list;
  (** [function_formals] maintains the relation between function identifiers
      and their formal arguments. *)
  function_formals : (S.function_identifier * S.formals) list;
}

(** Initially, the environment is empty. *)
let initial_environment () = {
  next_var         = 0;
  variables        = [];
  function_labels  = [];
  function_formals = [];
}

let initial_environment () = FopixToJavix.initial_environment ()

(* Lookups *)

exception Unbound_function_label of S.function_identifier
exception Unbound_function_formals of S.function_identifier
exception Unbound_variable of S.identifier

(** [lookup_function_label f env] returns the label of [f] in [env]. *)
let lookup_function_label f env =
  List.assoc f env.function_labels
    ~fexn:(fun x -> Unbound_function_label x)

(** [lookup_function_formals f env] returns the formal arguments of
    [f] in [env]. *)
let lookup_function_formals f env =
  List.assoc f env.function_formals
    ~fexn:(fun f -> Unbound_function_formals f)

(** [lookup_variabkes x env] returns the var of [x] in [env]. *)
let lookup_variable x env =
  List.assoc x env.variables
    ~fexn:(fun x -> Unbound_variable x)

(** [fresh_function_label f] returns a fresh label starting with [f]
    that will be used for the function body instructions. *)
let fresh_function_label =
  let r = ref 0 in
  fun f ->
    incr r;
    T.Label (f ^ "_body_" ^ string_of_int !r)

let fresh_label =
  let r = ref 0 in
  fun () ->
    incr r;
    T.Label ("_label_" ^ string_of_int !r)

let fresh_exit_label =
  let r = ref 0 in
  fun () ->
    incr r;
    T.Label ("_exit_label_" ^ string_of_int !r)

let fresh_env_id =
  let r = ref 0 in
  fun () ->
    incr r;
    "__env" ^ string_of_int !r

let fresh_block_id =
  let r = ref 0 in
  fun () ->
    incr r;
    "__block" ^ string_of_int !r

(** Variables *)

(** [bind_variable env x] associates Fopix variable x to the next
    Javix variable, and returns this variable and the updated
    environment *)

let bind_variable env x =
  let v = T.Var env.next_var in
  let new_env =
    { env with
      next_var = succ env.next_var;
      variables = (x,v) :: env.variables;
    }
  in (v,new_env)

let clear_all_variables env = {env with variables = []; next_var = 0}

(** For return addresses (or later higher-order functions),
    we encode some labels as numbers. These numbers could then
    be placed in the stack, and will be used in a final tableswitch *)

module Labels :
sig
  val encode : T.label -> int
  val all_encodings : unit -> (int * T.label) list
  val code : T.label -> int
end = struct
  let nextcode = ref 0
  let allcodes = ref ([]:(int * T.label) list)
  let encode lab =
    let n = !nextcode in
    incr nextcode;
    allcodes := (n,lab) :: !allcodes;
    n
  let all_encodings () = !allcodes
  let code lbl =
    fst @@ List.find (fun (_,lbl') -> lbl = lbl') !allcodes
end

let basic_program code = {
  T.classname = "Kontix";
  T.code = code;
  T.varsize = 100;
  T.stacksize = 10000;
}

(** [translate p env] turns a Kontix program [p] into a Javix program
    using [env] to retrieve contextual information. *)


module MACRO = struct
  (* some cppo could be nice fot this kind of thing ? *)
  let _TRUE_  = 1
  let _FALSE_ = 0
  let _RETURN_ = "_return_"
  let _K_ = "K"
  let _E_ = "E"
  module LABEL = struct
    let table_switch = Label "TABLE_SWITCH"
    let fail = Label "fail"
  end
end

(* Shortcuts *)

exception Conflict_labelling

let mk ?lbl x = (lbl,x)

let with_label ~lbl ?(strict=true) = function
  | (None,x) -> mk ~lbl x
  | (Some l,x) ->
    if strict
    then raise Conflict_labelling
    else mk ~lbl x

let push_label ~lbl xs = match xs with
  | [] -> failwith "push_label" (* or dummy ? *)
  | x::xs -> with_label ~lbl x :: xs

let unbox    = mk Unbox
let box      = mk Box
let swap     = mk Swap
let pop      = mk Pop
let ireturn  = mk Ireturn
let newarray = mk Anewarray

let checkarray  = mk Checkarray
let dup         = mk Dup
let aaload      = mk AAload
let aastore     = mk AAstore

let comment     ?lbl cmt        = mk ?lbl (Comment ("\"" ^ cmt ^ "\""))
let store       ?lbl var        = mk ?lbl (Astore var)
let goto        ?lbl lbl'       = mk ?lbl (Goto lbl')
let load        ?lbl var        = mk ?lbl (Aload var)
let bipush      ?lbl int        = mk ?lbl (Bipush int)
let if_icmpeq   ?lbl op lbl'    = mk ?lbl (If_icmp (op,lbl'))

let table_switch ?(lbl = Some MACRO.LABEL.table_switch) n lbls default =
  mk ?lbl (Tableswitch (n,lbls,default))

let comment_def id = comment ("Declaration of " ^ id)
let anchor ?(mess="ANCHOR") lbl = comment ~lbl mess

let after x y = x @ [y]

let load_unbox ?lbl var = after [load ?lbl var] unbox
let store_box  ?lbl var = after [box] (store ?lbl var)

let load_var   ?lbl id  = mk ?lbl (Aload (Var id))
let store_var  ?lbl id  = mk ?lbl (Astore (Var id))

let binop ?lbl op =
  let x = match op with
    | S.Add -> Add
    | S.Sub -> Sub
    | S.Mul -> Mul
    | S.Div -> Div
    | S.Mod -> Rem
    | _ -> failwith "binop"
  in mk ?lbl (Binop x)

let cmpop = function
  | S.Eq -> Eq
  | S.Lt -> Lt
  | S.Le -> Le
  | S.Gt -> Gt
  | S.Ge -> Ge
  | _ -> failwith "cmpop"

let kind_of_op = S.(function
    | Add | Sub | Mul | Div | Mod -> `Arith
    | Eq | Le | Lt | Ge | Gt -> `Cmp
  )

(* Debug *)

let print_env env =
  let open Printf in
  printf "next_var : %d\n" env.next_var;
  let xs = env.variables >|= fun (x, T.Var v) ->
    x ^ " -> " ^ string_of_int v
  in
  printf "variables : %s\n" (String.concat ";" xs);
  let xs = env.function_labels >|= fun (x, T.Label v) ->
    x ^ " -> " ^ v
  in
  printf "fun_labels : %s\n" (String.concat ";" xs);
  let xs = Labels.all_encodings () >|= fun (x, T.Label v) ->
    Printf.sprintf "ref(%d) -> %s" x v
  in
  printf "all_encodings : %s\n" (String.concat ";" xs)

(* [fail] considers 0 as error code *)

let fail = anchor ~mess:"Fail" MACRO.LABEL.fail :: bipush 0 :: [ireturn]

(* function_formals = (fid,xs)  :: env.function_formals; *)
let rec_mutual env = function
  | S.DefFun (fid,_,_)
  | S.DefCont (fid,_,_,_) ->
    let lbl = fresh_function_label fid in
    { env with function_labels  = (fid,lbl) :: env.function_labels }

let return_lbl = fresh_function_label MACRO._RETURN_

let finalizer v =
  let all_lbls =
    Labels.all_encodings ()
    |> List.sort (fun (r1,_) (r2,_) -> compare r1 r2)
    |> List.map snd
  in
  v @
  [comment ~lbl:return_lbl "return lbl"]
  @ [load (T.Var 2)]
  @ table_switch 0 all_lbls MACRO.LABEL.fail :: fail

let returnalize env =
  (* the final as in KontixToFopix *)
  let return_def exp = S.TDef (
      MACRO._K_,
      S.FunName MACRO._RETURN_,
      S.TDef (MACRO._E_, S.BlockNew (S.Num 0), exp)
    )
  in
  let new_env = {
    env with function_labels = (MACRO._RETURN_, return_lbl) :: env.function_labels
  } in                          (* ? *)
  let _n = Labels.encode return_lbl in  (* ? *)
  (new_env, return_def)

let rec translate (p : S.t) env =
  let (defs,exp) = p in
  let new_env = List.fold_left rec_mutual env defs in
  let prog = List.fold_left (fun acc def ->
      definition def new_env @ acc
    ) [] defs
  in
  let (new_env2, return) = returnalize new_env in
  let res = tailexpr new_env2 (return exp) in
  let final = finalizer res @ prog in
  print_env new_env;
  (basic_program final, new_env2)

and definition def env = match def with
  | S.DefFun (fid,fms,exp) ->
    (* get function label *)
    let lbl = lookup_function_label fid env in
    let enter = comment ~lbl ("enter_fun " ^ fid)  in
    (* new formals *)
    let new_fms = MACRO._K_ :: MACRO._E_ :: fms in
    (* bind formals *)
    let new_env = List.fold_left (fun acc x ->
        snd @@ bind_variable acc x
      ) env new_fms
    in enter :: tailexpr new_env exp

  | S.DefCont (fid,id,fm_env,texp) ->
    (* catch label *)
    let lbl = lookup_function_label fid env in
    (* labelize block *)
    let enter = comment ~lbl ("enter_fun " ^ fid)  in
    (* bind id and env *)
    let new_env =
      List.fold_left (fun acc x ->
          snd @@ bind_variable acc x
        ) env [MACRO._K_;MACRO._E_;id]
    in
    (* load continuation and store in var0 *)
    let kont =
      load (T.Var 1)
      :: checkarray
      :: bipush 0
      :: aaload
      :: [store (T.Var 0)]
    in
    (* load continuation_env and store in var1 *)
    let kenv =
      load (T.Var 1)
      :: checkarray
      :: bipush 1
      :: aaload
      :: [store (T.Var 1)]
    in
    enter :: unpopulate_block fm_env texp new_env kont kenv

and tailexpr env exp = match exp with

  | S.TDef (id,e1,e2) ->
    let c1 = basicexpr env e1 in
    let (v,new_env) = bind_variable env id in
    c1 @ [store v] @ tailexpr new_env e2

  | S.TIfThenElse (c,t,f) ->
    let lbl_t = fresh_label () in
    let lbl_f = fresh_label () in
    let c_code = basicexpr env c in
    let t_code = push_label ~lbl:lbl_t (tailexpr env t) in
    let f_code = push_label ~lbl:lbl_f (tailexpr env f) in
    c_code
    @ bipush 1 :: [if_icmpeq Eq lbl_t]
    @ f_code
    @ t_code

  | S.TFunCall (f,args,k) ->
    kont_env k env
    @ (args >>= basicexpr env)
    @ basicexpr env f
    @ [unbox]
    @ [goto MACRO.LABEL.table_switch]

  | S.TContCall (k,e) ->
    kont_env k env
    @ basicexpr env e
    @ [store (T.Var 2)]
    @ [load (T.Var 0)]
    @ [unbox]
    @ [goto MACRO.LABEL.table_switch]

and basicexpr env bexp = match bexp with

  | S.Num n ->
    after [bipush n] box

  | S.FunName fid ->
    let lbl = lookup_function_label fid env in
    let i = Labels.encode lbl in
    [bipush i; box]

  | S.Var id ->
    [load (lookup_variable id env)]

  | S.Def (id,e1,e2) ->
    let c1 = basicexpr env e1 in
    let (v,new_env) = bind_variable env id in
    c1 @ [store v] @ basicexpr new_env e2

  | S.IfThenElse (c,t,f) ->
    let lbl_exit = fresh_exit_label () in
    let lbl_t = fresh_label () in
    let lbl_f = fresh_label () in
    let exit = goto lbl_exit in
    let c_code = basicexpr env c in
    let t_code = push_label ~lbl:lbl_t (basicexpr env t) in
    let f_code = push_label ~lbl:lbl_f (basicexpr env f) in
    c_code
    @ comment "push true" :: bipush 1 :: [if_icmpeq Eq lbl_t]
    @ after f_code exit
    @ t_code
    @ [anchor lbl_exit]

  | S.BinOp (op,e1,e2) -> begin match kind_of_op op with
      | `Arith ->
        let c1 = basicexpr env e1 in
        let c2 = basicexpr env e2 in
        c1 @ unbox :: c2 @ unbox :: [binop op; box]
      | `Cmp ->
        let c1 = basicexpr env e1 in
        let c2 = basicexpr env e2 in
        let lbl_t = fresh_label () in
        let lbl_exit = fresh_exit_label () in
        let exit = goto lbl_exit in
        let t = [bipush ~lbl:lbl_t MACRO._TRUE_] in
        let f = [bipush MACRO._FALSE_] in
        (* Exchange c2 and c1 because of the following swap instruction *)
        c2 @ [unbox] @
        c1 @ [unbox] @
        swap :: [if_icmpeq (cmpop op) lbl_t]
        @ after f exit
        @ t
        @ [anchor lbl_exit]
    end

  | S.BlockNew e ->
    basicexpr env e @ unbox :: [newarray]

  | S.BlockGet (t,i) ->
    basicexpr env t
    @ [checkarray]
    @ basicexpr env i
    @ [unbox]
    @ [aaload]

  | S.BlockSet (t,i,e) ->
    basicexpr env t
    @ [checkarray]
    @ basicexpr env i
    @ [unbox]
    @ basicexpr env e
    @ [aastore]
    @ [bipush 0;box]

and kont_env cont env = match cont with

  | S.CurCont -> []

  | S.PushCont (fid,k,ids) ->
    let f_push =
      let lbl = lookup_function_label fid env in
      let i = Labels.encode lbl in
      [bipush i;box]           (* fixme ? box *)
    in
    (* block id *)
    let block_init =
      let l = 2 + List.length ids in (* k :: e :: ids *)
      load (T.Var 1) :: checkarray :: bipush l :: [newarray]
    in
    (* fixme *)
    let block_body =
      store (T.Var 1)
      :: load (T.Var 1)
      :: checkarray
      :: swap
      :: bipush 1
      :: swap
      :: aastore
      :: load (T.Var 1)
      :: bipush 0
      :: load (T.Var 0)
      :: [aastore]
    in
    let block_full = block_init @ block_body in
    kont_env cont env
    @ block_full
    @ populate_block ids env
    @ f_push

and populate_block ids env =
  let rec aux i = function
    | [] -> []
    | id :: ids ->
      [load (T.Var 1)]
      @ [checkarray]
      @ [bipush i]
      @ [load (lookup_variable id env)]
      @ [aastore]
      @ aux (succ i) ids
  in aux 2 ids

and unpopulate_block ids res env kont kenv =
  let rec aux i env = function
    | [] ->
      kont @
      kenv @
      tailexpr env res
    | id :: ids ->
      let (T.Var v,new_env) = bind_variable env id in
      [bipush 1]
      @ [aaload]
      @ [checkarray]
      @ [bipush i]
      @ [aaload]
      @ [store (T.Var (succ v))]
      @ aux (succ i) new_env ids
  in aux 2 env ids

let rec translate (p : S.t) env =
  let p = KontixToFopix.program p in
  (FopixToJavix.translate p env)
