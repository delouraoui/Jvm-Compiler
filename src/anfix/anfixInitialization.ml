module RealFopixToAnfix = struct
  module Source=Fopix
  module Target=Anfix
  type environment = unit
  let initial_environment () = ()
  let translate ast () = FopixToAnfix.program ast, ()
end

let initialize () =
  Compilers.register "anfix" "anfix"
    (module Compilers.Identity (Anfix) : Compilers.Compiler);
  Compilers.register "fopix" "anfix"
    (module RealFopixToAnfix : Compilers.Compiler)
