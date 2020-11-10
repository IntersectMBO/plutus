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

  # The haskell project created by haskell-nix.stackProject'
  project = import ../../haskell.nix {
    inherit lib stdenv haskell-nix buildPackages nix-gitignore R rPackages z3;
    inherit agdaWithStdlib checkMaterialization;
  };

  # All the packages defined by our project, including dependencies
  packages = project.hsPkgs;

  # Just the packages in the project
  projectPackages = haskell-nix.haskellLib.selectProjectPackages packages
    # Need to list this manually to work around https://github.com/input-output-hk/haskell.nix/issues/464
    // { inherit (packages) plutus-metatheory; };


  # The haskell project created by haskell-nix.stackProject' (musl version)
  muslProject = import ../../haskell.nix {
    inherit (pkgsMusl) lib stdenv haskell-nix buildPackages nix-gitignore R rPackages z3;
    inherit agdaWithStdlib checkMaterialization;
  };

  # All the packages defined by our project, built for musl
  muslPackages = muslProject.hsPkgs;

  extraPackages = import ./extra.nix {
    inherit lib haskell-nix fetchFromGitHub fetchFromGitLab index-state checkMaterialization buildPackages;
  };

in
rec {
  inherit index-state project projectPackages packages;
  inherit muslProject muslPackages;
  inherit extraPackages;
}
