let
  local = import ../. {};
in
local.localLib.withDevTools local.localPackages.marlowe.env
