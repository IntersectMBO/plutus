# TODO: replace with shellFor once our pinned nixpkgs advances past
# 5523ec8f3c78704c6e76b7675bfce41d24a3feb1, before which it doesn't
# handle overridden dependencies properly
let
  localLib = import ./lib.nix;
in
{ system ? builtins.currentSystem
, config ? {}
, pkgs ? (import (localLib.fetchNixPkgs) { inherit system config; })
}:

let
  plutusPkgs = import ./. {};
  ghc = pkgs.haskell.packages.ghc822.ghcWithPackages (ps: [
    plutusPkgs.plutus-prototype
    plutusPkgs.language-plutus-core
    plutusPkgs.tasty-hedgehog
    plutusPkgs.tasty
    plutusPkgs.tasty-golden
    plutusPkgs.tasty-hunit
    plutusPkgs.hedgehog
  ]);
  fixStylishHaskell = pkgs.stdenv.mkDerivation {
    name = "fix-stylish-haskell";
    buildInputs = with pkgs; [ plutusPkgs.stylish-haskell git ];
    shellHook = ''
      git diff > pre-stylish.diff
      find . -type f -name "*hs" -not -path '.git' -not -path '*.stack-work*' -not -path '*/dist/*' -not -path '*/docs/*' -not -name 'HLint.hs' -exec stylish-haskell -i {} \;
      git diff > post-stylish.diff
      diff pre-stylish.diff post-stylish.diff > /dev/null
      if [ $? != 0 ]
      then
        echo "Changes by stylish have been made. Please commit them."
      else
        echo "No stylish changes were made."
      fi
      rm pre-stylish.diff post-stylish.diff
      exit
    '';
  };

in
  # This is an environment for running the deps regeneration script.
  pkgs.stdenv.mkDerivation {
    name = "plutus-ghc";
    passthru = { inherit fixStylishHaskell; };
    buildInputs = with pkgs; [ ghc ];
    src = null;
  }
