let 
  local = import ../. {};
in
local.localLib.withDevTools local.localPackages.language-plutus-core.env
