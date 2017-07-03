(* todo : improve tailcall *)
(* todo : add tests *)

(* Toolkit *)

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

(** This module implements a compiler from Fopix to Javix. *)

let error pos msg =
  Error.error "compilation" pos msg

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)
module Source = Fopix
module Target = Javix

module S = Source.AST
module T = Target.AST

(** We will need the following pieces of information to be carrying
    along the translation: *)
type environment = {
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
end
=
struct
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
  T.classname = "Fopix";
  T.code = code;
  T.varsize = 100;
  T.stacksize = 10000;
}

(** [translate p env] turns a Fopix program [p] into a Javix program
    using [env] to retrieve contextual information. *)


(** Remarks:
    - When using this compiler from fopix to javix, flap will
    produce some .j files.
    + Compile them to .class via: jasmin Foobar.j
    + Run them with: java -noverify Foobar

    - Final answer:
    your code should contain a final [Ireturn] that should
    return the value of the last DefineValue (supposed to be
    an Integer).

    - Function Call Convention:
    + The n arguments should be in jvm's variables 0,1,...(n-1).
    + At least the variables that are reused after this call
      should have their contents saved in stack before the call
      and restored afterwards.
    + Just before the function call, the return address should
      be placed on the stack (via the encoding as number of this
      return label, see Labels.encode).
    + When the function returns, the result should be on the top
      of the stack.

    - Boxing:
    The stack could contain both unboxed elements (Java int)
    or boxed elements (Java objects such as Integer or java arrays).
    We place into variables or in array cells only boxed values.
    The arithmetical operations (iadd, if_icmpeq, ...) only works
    on unboxed numbers.
    Conversion between int and Integer is possible via the
    Box and Unboxed pseudo-instructions (translated into correct
    calls to some ad-hoc methods we provide). You may try to
    do some obvious optimisations such as removing [Box;Unbox] or
    [Unbox;Box].

    - Tail-recursive calls : if the body of f ends with a call to
    another function g (which may be f itself in case of recursion),
    no need to save any variables, nor to push a new return address:
    just reuse the return address of the current call to f when
    jumping to g !

    - Variable size and stack size
    Your code should determine the number of variables used by the
    produced code. You might also try to compute the maximum
    stack size when the code is non-recursive or 100% tail-recursive.
*)

open T

module MACRO = struct
  (* some cppo could be nice fot this kind of thing ? *)
  let _TRUE_  = 1
  let _FALSE_ = 0
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
let aaload      = mk AAload
let aastore     = mk AAstore

let comment     ?lbl cmt        = mk ?lbl (Comment ("\"" ^ cmt ^ "\""))
let store       ?lbl var        = mk ?lbl (Astore var)
let goto        ?lbl lbl'       = mk ?lbl (Goto lbl')
let load        ?lbl var        = mk ?lbl (Aload var)
let bipush      ?lbl int        = mk ?lbl (Bipush int)
let if_icmpeq   ?lbl op lbl'    = mk ?lbl (If_icmp (op,lbl'))

let table_switch ?(lbl=Some MACRO.LABEL.table_switch) n lbls default =
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

let finalizer v =
  let all_lbls =
    Labels.all_encodings ()
    |> List.sort (fun (r1,_) (r2,_) -> compare r1 r2)
    |> List.map snd
  in
  comment "Finalizer" ::
  load_unbox v @
  ireturn ::
  table_switch 0 all_lbls MACRO.LABEL.fail ::
  fail

(* Analyse and optimize [DRAFT : todo] *)

module Analyse = struct

  type ('a,'b) either =
    | Left of 'a
    | Right of 'b

  let active = ref false

  let activate () = (active := true)

  let backtrack acc xs = match acc with
    | y::ys -> (ys,y::xs)
    | [] -> ([],xs)

  type optim = {
    priority: int;
    backtrack: int;
    additional_inst: instruction option
  }

  let mk_optim ~backtrack ~additional_inst ~priority = {
    priority;
    backtrack;
    additional_inst;
  }

  let rules2 i1 i2 = match (snd i1, snd i2) with
    | Box,Unbox | Unbox,Box ->
      Right (mk_optim ~backtrack:1 ~additional_inst:None ~priority:1)
    | Aload a, Astore b when a = b ->
      Right (mk_optim ~backtrack:1 ~additional_inst:None ~priority:1)
    | _ ->
      Left (i1,i2)

  let rec give n code acc =
    if n = 0 then (code,acc)
    else match acc with
      | i :: is -> give (pred n) (i::code) is
      | [] -> (code,acc)

  let optimize opt code acc = match opt with
    | Right optim ->
      give optim.backtrack code acc
    | Left (i1,i2) ->
      (i2::code,i1::acc)

  let run p =
    if not !active then p
    else
      let rec loop (code,acc) = match code with
        | [] -> List.rev acc
        | i1 :: i2 :: is ->
          let (new_code,new_acc) = optimize (rules2 i1 i2) is acc
          in loop (new_code,new_acc)
        | i :: is ->
          loop (is,i::acc)
      in {p with code = loop (p.code,[])}
end

(* The wrapper splits the program between simple definitions and function
   declarations.
*)

module Wrap = struct

  type t = {
    run : labelled_instruction list;
    on_demand : labelled_instruction list;
  }

  let empty = {run = []; on_demand = []}

  let dispatch tag prog is = match tag with
    | `run ->
      {prog with run = prog.run @ is}
    | `on_demand ->
      {prog with on_demand = prog.on_demand @ is}

  let glue_with sep prog =
    prog.run @ sep @ prog.on_demand

end

(* ENTRANCE *)

let rec_mutual env = function
  | S.DefVal (id,exp) ->
    let (_var,new_env) = bind_variable env id in
    new_env

  | S.DefFun (fid,xs,e) ->
    let lbl = fresh_function_label fid in
    let new_env = {
      env with
      function_formals = (fid,xs)  :: env.function_formals;
      function_labels  = (fid,lbl) :: env.function_labels;
    } in
    new_env


(* The tailcall optimization is handled by the [tailcall] function. *)

let rec translate p env : T.t * environment =
  let env = List.fold_left rec_mutual (initial_environment ()) p in
  let (prog,env) =
    List.fold_left (fun (prog,env) def ->
        let (tag,code0,env0) = definition def env in
        (Wrap.dispatch tag prog code0, env0)
      ) (Wrap.empty,env) p
  in
  let last_pos = Var (pred env.next_var) in
  let collapsed = Wrap.glue_with (finalizer last_pos) prog in
  let program = basic_program collapsed in
  print_env env;
  Analyse.activate ();
  let opt_program = Analyse.run program in
  (opt_program,env)

and definition def env = match def with

  | S.DefVal (id,exp) ->
    let var = lookup_variable id env in
    let c = expression env exp in
    (`run, comment_def id :: c @ [store var], env)

  | S.DefFun (fid,xs,e) ->
    let lbl = lookup_function_label fid env in
    let enter = comment ~lbl ("enter_fun " ^ fid)  in
    let (stored,new_env) =
      List.fold_left (fun (acc,env) x ->
          let (v,new_env) = bind_variable env x in
          ([store v] @ acc, new_env)
        ) ([],env) xs
    in
    let body = (* expression  *)tailcall new_env e in
    let code =
      enter
      :: stored
      @ body
      @ [swap]
      @ [comment "this unbox in defun"]
      @ [unbox]
      @ [goto MACRO.LABEL.table_switch]
    in
    (`on_demand,code,env)

and expression env exp = match exp with
  | S.Num n ->
    after [bipush n] box

  | S.Var id ->
    comment ("lookup " ^ id) ::
    [load (lookup_variable id env)]

  (* factorize this ! *)
  | S.FunCall (S.FunName fid,es) ->
    let ctx = List.init (pred env.next_var) (fun x -> Var (succ x)) in
    let save_ctx = ctx >|= load in
    let restore_ctx = ctx >>= fun x -> swap :: [store x] in
    let args_code = es >>= expression env in
    let lbl = fresh_label () in
    let return = comment ~lbl ("#return from " ^ fid)  in
    let return_address = [bipush (Labels.encode lbl)] in
    let call = [goto (lookup_function_label fid env)] in
    save_ctx
    @ return_address
    @ [box]
    @ args_code
    @ call
    @ return :: restore_ctx

  | S.FunCall (f,es) ->
    let ctx = List.init (pred env.next_var) (fun x -> Var (succ x)) in
    let save_ctx = ctx >|= load in
    let restore_ctx = ctx >>= fun x -> swap :: [store x] in
    let args_code = es >>= expression env in
    let lbl = fresh_label () in
    let return = comment ~lbl "#return" in
    let return_address = [bipush (Labels.encode lbl)] in
    save_ctx
    @ return_address
    @ [box]
    @ args_code
    @ expression env f
    @ [unbox]
    @ [goto MACRO.LABEL.table_switch]
    @ return :: restore_ctx

  | S.FunName fid ->
    comment ("Funame" ^ fid) ::
    let lbl = lookup_function_label fid env in
    let i = Labels.encode lbl in
    [bipush i ; box]

  | S.Def (x,e1,e2) ->
    let c1 = expression env e1 in
    let (v,new_env) = bind_variable env x in
    c1 @ store v :: expression new_env e2

  | S.IfThenElse (c,t,f) ->
    [comment "If then else"]
    @
    (* exit, true and false labels *)
    let lbl_exit = fresh_exit_label () in
    let lbl_t = fresh_label () in
    let lbl_f = fresh_label () in
    (* exit, condition, true and false code parts *)
    let exit = goto lbl_exit in
    let c_code = expression env c in
    let t_code = push_label ~lbl:lbl_t (expression env t) in
    let f_code = push_label ~lbl:lbl_f (expression env f) in
    (* and so.. *)
    c_code
    @ comment "push true" :: bipush 1 :: [if_icmpeq Eq lbl_t]
    @ after f_code exit
    @ t_code
    @ [anchor lbl_exit]

  | S.BinOp (op,e1,e2) ->
    [comment "Bin op"]
    @
    begin match kind_of_op op with
      | `Arith ->
        let c1 = expression env e1 in
        let c2 = expression env e2 in
        c1 @ unbox :: c2 @ unbox :: [binop op; box]
      | `Cmp ->
        let c1 = expression env e1 in
        let c2 = expression env e2 in
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
    [comment "Block New"]
    @
    expression env e @ unbox :: [newarray]

  | S.BlockGet (t,i) ->
    [comment "Block get"]
    @
    expression env t
    @ [checkarray]
    @ expression env i
    @ [unbox]
    @ [aaload]

  | S.BlockSet (t,i,e) ->
    [comment "Block set"]
    @
    expression env t
    @ [checkarray]
    @ expression env i
    @ [unbox]
    @ expression env e
    @ [aastore]
    (* Since "t[i]=M;.." == "def () = t[i] := M in ..", we
       are forced to push a dummy value on the stack.. *)
    @ [bipush 0;box]

and tailcall env exp = match exp with

  | S.FunCall (S.FunName fid,args) ->
    let args_code = args >>= expression env in
    let call = [goto (lookup_function_label fid env)] in
    args_code @ call

  | S.FunCall (f,es) ->
    [comment "tailcall - funcall "]
    @ (es >>= expression env)
    @ expression env f
    @ [unbox]
    @ [goto MACRO.LABEL.table_switch]

  | S.Def (x,e1,e2) ->
    let c1 = expression env e1 in
    let (v,new_env) = bind_variable env x in
    c1 @ [store v] @ tailcall new_env e2

  | S.IfThenElse (c,t,f) ->
    (* exit, true and false labels *)
    let lbl_exit = fresh_exit_label () in
    let lbl_t = fresh_label () in
    let lbl_f = fresh_label () in
    (* exit, condition, true and false code parts *)
    let exit = goto lbl_exit in
    let c_code = expression env c in
    let t_code = push_label ~lbl:lbl_t (tailcall env t) in
    let f_code = push_label ~lbl:lbl_f (tailcall env f) in
    (* and so.. *)
    c_code
    @ comment "push _true" :: bipush 1 :: [if_icmpeq Eq lbl_t]
    @ after f_code exit
    @ t_code
    @ [anchor lbl_exit]

  | expr -> expression env expr
