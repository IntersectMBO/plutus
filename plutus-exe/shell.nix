let 
  local = import ../. {};
in
local.localLib.withDevTools local.localPackages.plutus-exe.env
