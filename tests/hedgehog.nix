{ pkgs, plutusPkgs, runCommand, source }:

let
  ghc = pkgs.haskell.packages.ghc822.ghcWithPackages (ps: [
    plutusPkgs.plutus-prototype 
    plutusPkgs.language-plutus-core 
    plutusPkgs.tasty-hedgehog
    plutusPkgs.tasty
    plutusPkgs.tasty-golden
    plutusPkgs.tasty-hunit
    plutusPkgs.hedgehog
  ]);

in
  runCommand "plutus-hedgehog-tests" { buildInputs = [ ghc ]; } ''
    pushd ${source}/language-plutus-core
    runhaskell test/Spec.hs
    EXIT_CODE=$?
    if [ $EXIT_CODE == 0 ]
    then
      echo $EXIT_CODE > $out 
      exit 0
    fi
  ''
