(** The main driver module.

    The role of this module is to have [flap] behave as
    the command line options say. In particular, these
    options determine:

    - if the compiler is run in interactive or batch mode.
    - what is the source language of the compiler.
    - what is the target language of the compiler.

*)

(** -------------------------- **)
(**   Initialization process    *)
(** -------------------------- **)

open Options

let rec initialize () =
  initialize_options ();
  initialize_languages ();
  initialize_prompt ();

and initialize_prompt () =
  UserInput.set_prompt "flap> "

and initialize_options () =
  CommandLineOptions.parse ()

and initialize_languages () =
  FopixInitialization.initialize ();
  AnfixInitialization.initialize ();
  KontixInitialization.initialize ();
  JakixInitialization.initialize ();
  JavixInitialization.initialize ()

let get_source_target () =
  let source_language =
    get_source_language ()
  in
  let target_language =
    if is_target_language_set () then
      get_target_language ()
    else
      source_language
  in
  source_language, target_language

let get_compiler () =
  let (s,t) = get_source_target () in Compilers.get s t

let get_compilers () =
  let (s,t) = get_source_target () in
  if s = t then [Compilers.get s t] else Compilers.chain s t

let eval runtime eval print =
  let now = Unix.gettimeofday () in
  let runtime, observation = eval runtime in
  let elapsed_time = Unix.gettimeofday () -. now in
  if Options.get_benchmark () then
    print_endline ("(" ^ string_of_float elapsed_time ^ "s)");
  print_endline (print runtime observation);
  runtime

(** -------------------- **)
(**   Interactive mode    *)
(** -------------------- **)
(**

   The interactive mode is a basic read-compile-eval-print loop.

*)
let interactive_loop () =

  Printf.printf "        Flap version %s\n\n%!" Version.number;

  let module Compiler = (val get_compiler () : Compilers.Compiler) in
  let open Compiler in

  let read () =
    initialize_prompt ();
    let b = Buffer.create 13 in
    let rec read prev =
      let c = UserInput.input_char stdin in
      if c = "\n" then
        if prev <> "\\" then (
          Buffer.add_string b prev;
          Buffer.contents b
        ) else (
          UserInput.set_prompt "....> ";
          read c
        )
      else (
        Buffer.add_string b prev;
        read c
      )
    in
    read ""
  in

  let rec step
    : Target.runtime -> Compiler.environment -> Source.typing_environment
    -> Target.runtime * Compiler.environment * Source.typing_environment =
    fun runtime cenvironment tenvironment ->
      try
        match read () with
          | "+debug" ->
            Options.set_verbose_mode true;
            step runtime cenvironment tenvironment

          | "-debug" ->
            Options.set_verbose_mode false;
            step runtime cenvironment tenvironment

          | input ->
            let ast = Compiler.Source.parse_string input in
            let tenvironment =
              if Options.get_unsafe () then
                tenvironment
              else
                Compiler.Source.typecheck tenvironment ast
            in
            let cast, cenvironment = Compiler.translate ast cenvironment in
            if Options.get_verbose_mode () then
              print_endline (Target.print_ast cast);
            let runtime = Compiler.Target.(
              eval runtime (fun r -> evaluate r cast) print_observable
            )
            in
            step runtime cenvironment tenvironment
      with
        | Error.Error (positions, msg) ->
          output_string stdout (Error.print_error positions msg);
          step runtime cenvironment tenvironment
        | End_of_file ->
          (runtime, cenvironment, tenvironment)
        | e ->
          print_endline (Printexc.to_string e);
          step runtime cenvironment tenvironment
  in
  Error.resume_on_error ();
  ignore (step
            (Target.initial_runtime ())
            (Compiler.initial_environment ())
            (Source.initial_typing_environment ())
  )

(** ------------- **)
(**   Batch mode   *)
(** ------------- **)
(**

   In batch mode, the compiler loads a file written in the source
   language and writes one file per intermediate language until
   the target language is reached.

   The filenames of the output files are determined by the basename
   of the input filename concatenated with the extension of the
   intermediate and target languages.

   If the running mode is set, the compiler will also interpret
   the final compiled code (using the target interpretor).
*)

let batch_compilation () =
  Error.exit_on_error ();
  let input_filename = Options.get_input_filename () in
  let module_name = Filename.chop_extension input_filename in
  let () = Options.compilation_unit_name := module_name
  in
  let one_compilation infile c last =
    let module Compiler = (val c : Compilers.Compiler) in
    let ast = Compiler.Source.parse_filename infile in
    if Options.get_unsafe () then
      ()
    else
      ignore (Compiler.Source.(typecheck (initial_typing_environment ()) ast));
    let cast, _ = Compiler.(translate ast (initial_environment ())) in
    let output_filename = module_name ^ Compiler.Target.extension in
    if not (Options.get_dry_mode ()) then (
      let cout = open_out output_filename in
      output_string cout (Compiler.Target.print_ast cast);
      close_out cout;
    );
    if last && Options.get_running_mode () then Compiler.Target.(
      ignore (
        try
          eval (initial_runtime ()) (fun r -> evaluate r cast) print_observable
        with
        | e ->
          print_endline (Printexc.to_string e);
          exit 1
      )
    );
    output_filename
  in
  let rec many_compilations infile = function
    | [] -> assert false
    | [c] -> ignore (one_compilation infile c true)
    | c::lc ->
      let midfile = one_compilation infile c false in
      many_compilations midfile lc
  in
  many_compilations input_filename (get_compilers ())

(** -------------- **)
(**   Entry point   *)
(** -------------- **)
let main =
  initialize ();
  match get_mode () with
    | Interactive -> interactive_loop ()
    | Batch -> batch_compilation ()
