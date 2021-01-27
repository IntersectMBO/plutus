{ supportedSystems ? [ "x86_64-linux" "x86_64-darwin" ]
  # Passed in by Hydra depending on the configuration, contains the revision and the out path
, plutus ? null
}:
let
  # The revision passed in by Hydra, if there is one
  rev = if builtins.isNull plutus then null else plutus.rev;

  inherit (import ./nix/lib/ci.nix) stripAttrsForHydra filterDerivations derivationAggregate;

  ci = import ./ci.nix { inherit supportedSystems rev; };
  # ci.nix is a set of attributes that work fine as jobs (albeit in a slightly different structure, the platform comes
  # first), but we mainly just need to get rid of some extra attributes.
  ciJobsets = stripAttrsForHydra (filterDerivations ci);
in
ciJobsets // { required = derivationAggregate "required-plutus" ciJobsets; }
