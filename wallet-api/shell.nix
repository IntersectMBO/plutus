let 
  local = import ../. {};
in
local.localLib.withDevTools local.localPackages.wallet-api.env
