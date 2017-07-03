let initialize () =
  Compilers.register "jakix" "jakix"
    (module Compilers.Identity (Jakix) : Compilers.Compiler);
  Compilers.register "kontix"  "jakix"
    (module KontixToJakix : Compilers.Compiler)
