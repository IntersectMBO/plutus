{ lib, mkDerivation, standard-library }:
let
in
mkDerivation {
  pname = "Plutus";
  version = "0.1";

  src = lib.sourceFilesBySuffices ./. [ ".agda" ".lagda" ".lagda.md" ".agda-lib" ];

  buildInputs = [ standard-library ];

  everythingFile = "Everything.lagda";
}
