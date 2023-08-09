{ inputs, cell }:

cell.library.build-latex-doc {
  name = "plutus-core-spec";
  description = "Plutus core specification";
  src = inputs.self + /doc/plutus-core-spec;
  texFiles = [ "plutus-core-specification.tex" ];
}
