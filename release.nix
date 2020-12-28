{ supportedSystems ? [ "x86_64-linux" "x86_64-darwin" ]
  # Passed in by Hydra depending on the configuration, contains the revision and the out path
, plutus ? null
}:
let
  # The revision passed in by Hydra, if there is one
  rev = if builtins.isNull plutus then null else plutus.rev;

  # Generic nixpkgs for library usage
  genericPkgs = import (import ./nix/sources.nix).nixpkgs { };
  lib = genericPkgs.lib;

  inherit (import ./nix/lib/ci.nix) stripAttrsForHydra filterDerivations;

  ci = import ./ci.nix { inherit supportedSystems rev; };
  # ci.nix is a set of attributes that work fine as jobs (albeit in a slightly different structure, the platform comes
  # first), but we mainly just need to get rid of some extra attributes.
  ciJobsets = stripAttrsForHydra (filterDerivations ci);
  # Recursively collect all jobs (derivations) in a jobset
  # This uses 'attrByPath' so we can give a default if the attr is missing, which can happen
  # if you've set 'supportedSystems' to not include all the systems.
  allJobs = path: jobset: lib.collect lib.isDerivation (lib.attrByPath path { } jobset);
in
lib.fix (jobsets: ciJobsets // {
  required = lib.hydraJob (genericPkgs.releaseTools.aggregate {
    name = "plutus-required-checks";

    constituents =
      # Misc tests
      (allJobs [ "linux" "tests" ] jobsets)
        ++ (allJobs [ "darwin" "tests" ] jobsets)
        # Haskell tests
        ++ (allJobs [ "linux" "haskell" ] jobsets)
        ++ (allJobs [ "darwin" "haskell" ] jobsets)
        # Various things that mostly just need to build on linux
        ++ (allJobs [ "linux" "docs" ] jobsets)
        ++ (allJobs [ "linux" "docs" "papers" ] jobsets)
        ++ (allJobs [ "linux" "plutus-playground" ] jobsets)
        ++ (allJobs [ "linux" "marlowe-playground" ] jobsets)
        ++ (allJobs [ "darwin" "plutus-playground" ] jobsets)
        ++ (allJobs [ "darwin" "marlowe-playground" ] jobsets)
        ++ (allJobs [ "linux" "plutus-scb" ] jobsets)
        # deployment tools
        ++ (allJobs [ "darwin" "thorp" ] jobsets)
        ++ (allJobs [ "linux" "thorp" ] jobsets)
        # Shell environment so it never breaks
        ++ (if (lib.hasAttrByPath [ "linux" "shell" ] jobsets) then [ jobsets.linux.shell ] else [ ])
        ++ (if (lib.hasAttrByPath [ "darwin" "shell" ] jobsets) then [ jobsets.darwin.shell ] else [ ]);
  });
})
