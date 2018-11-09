# TODO: replace with shellFor once our pinned nixpkgs advances past
# 5523ec8f3c78704c6e76b7675bfce41d24a3feb1, before which it doesn't
# handle overridden dependencies properly
let
  localLib = import ./lib.nix;
in
{ system ? builtins.currentSystem
, config ? {}
, pkgs ? (import (localLib.fetchNixpkgs) { inherit system config; })
}:

let
  plutusPkgs = import ./. {};
  fixStylishHaskell = pkgs.stdenv.mkDerivation {
    name = "fix-stylish-haskell";
    buildInputs = with pkgs; [ haskellPackages.stylish-haskell git fd ];
    shellHook = ''
      git diff > pre-stylish.diff
      fd --extension hs --exclude '*/dist/*' --exclude '*/docs/*' --exec stylish-haskell -i {}
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
  shell = plutusPkgs.haskellPackages.shellFor {
    packages = p: (map (x: p.${x}) localLib.plutusPkgList);
  };

in shell // {
  inherit fixStylishHaskell;
}
