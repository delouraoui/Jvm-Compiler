(** Compilers. *)

open Languages

(** A compiler translates programs from a source language
    into programs of a target language. *)
module type Compiler = sig

  module Source : Language
  module Target : Language

  type environment
  val initial_environment : unit -> environment

  val translate : Source.ast -> environment -> Target.ast * environment

end

(** Compiler implementations are stored in the following
    hashing table. *)
let compilers : (string * string, (module Compiler)) Hashtbl.t =
  Hashtbl.create 31

let register source target m =
  Hashtbl.add compilers (source, target) m

let get source target =
  try
    Hashtbl.find compilers (source, target)
  with Not_found ->
    Error.global_error
      "during compilation"
      "Sorry, there is no such compiler in flap."

(* Search for a compiler chain : source -> lang2 -> ... langk -> target
   We assume for now that only one path leads to a given language
   (apart from identity compiler). The code below is inefficient,
   but we don't care for the moment (less that 10 languages max...)
*)

let chain source target =
  let lookup target =
    Hashtbl.fold
      (fun (s,t) c o -> if t=target && s<>t then Some (s,t,c) else o)
      compilers None
  in
  let rec loop source target =
    match lookup target with
    | Some (s,t,c) when s=source -> [c]
    | Some (s,t,c) -> c :: loop source s
    | None ->
      Error.global_error
        "during compilation"
        "Sorry, there is no such compiler in flap."
  in
  List.rev (loop source target)


(** There is an easy way to compile a language into itself:
    just use the identity function :-). *)
module Identity (L : Language) : Compiler = struct
  module Source = L
  module Target = L
  type environment = unit
  let initial_environment () = ()
  let translate x () = (x, ())
end
