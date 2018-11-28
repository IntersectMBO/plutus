let 
  local = import ../. {};
in
local.localLib.withDevTools local.localPackages.plutus-core-interpreter.env
