let initialize () =
  Compilers.register "kontix" "kontix"
    (module Compilers.Identity (Kontix) : Compilers.Compiler);
  Compilers.register "anfix" "kontix"
    (module AnfixToKontix : Compilers.Compiler)
