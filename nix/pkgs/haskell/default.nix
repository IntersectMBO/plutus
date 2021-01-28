{ lib
, fetchFromGitHub
, fetchFromGitLab
, agdaWithStdlib
, pkgsMusl
, stdenv
, haskell-nix
, buildPackages
, checkMaterialization
, nix-gitignore
, R
, rPackages
, z3
, enableHaskellProfiling
}:
let
  # The Hackage index-state from cabal.project
  index-state =
    let
      parseIndexState = rawCabalProject:
        let
          indexState = lib.lists.concatLists (
            lib.lists.filter (l: l != null)
              (map (l: builtins.match "^index-state: *(.*)" l)
                (lib.splitString "\n" rawCabalProject)));
        in
        lib.lists.head (indexState ++ [ null ]);
    in
    parseIndexState (builtins.readFile ../../../cabal.project);

  # The compiler that we are using. We are using a patched version so we need to specify it explicitly.
  # This version has the experimental core interface files patch, and a fix for unboxed tuples in
  # GHCi, which helps with HLS.
  compiler-nix-name = "ghc810220201118";

  # The haskell project created by haskell-nix.stackProject'
  project = import ./haskell.nix {
    inherit lib stdenv haskell-nix buildPackages nix-gitignore R rPackages z3;
    inherit agdaWithStdlib checkMaterialization compiler-nix-name;
    inherit enableHaskellProfiling;
  };

  # All the packages defined by our project, including dependencies
  packages = project.hsPkgs;

  # Just the packages in the project
  projectPackages = haskell-nix.haskellLib.selectProjectPackages packages
    # Need to list this manually to work around https://github.com/input-output-hk/haskell.nix/issues/464
    // { inherit (packages) plutus-metatheory; };


  # The haskell project created by haskell-nix.stackProject' (musl version)
  muslProject = import ./haskell.nix {
    inherit (pkgsMusl) lib stdenv haskell-nix buildPackages nix-gitignore R rPackages z3;
    inherit agdaWithStdlib checkMaterialization compiler-nix-name;
    inherit enableHaskellProfiling;
  };

  # All the packages defined by our project, built for musl
  muslPackages = muslProject.hsPkgs;

  extraPackages = import ./extra.nix {
    inherit stdenv lib haskell-nix fetchFromGitHub fetchFromGitLab buildPackages;
    inherit index-state checkMaterialization compiler-nix-name;
  };

in
rec {
  inherit index-state project projectPackages packages;
  inherit muslProject muslPackages;
  inherit extraPackages;
}
