let
  localLib = import ./lib.nix;
in
{ system ? builtins.currentSystem
, config ? {}
, pkgs ? (import (localLib.iohkNix.nixpkgs) { inherit system config; })
}:

let
  localPackages = import ./. {};
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
  shell = localPackages.haskellPackages.shellFor {
    packages = p: (map (x: p.${x}) localLib.plutusPkgList);
    nativeBuildInputs = [ pkgs.cabal-install pkgs.haskellPackages.ghcid ];
  };

in shell // {
  inherit fixStylishHaskell;
}
