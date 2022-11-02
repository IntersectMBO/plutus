{ inputs, cell }:

cell.library.build-latex-doc {
  name = "plutus-report";
  description = "plutus report";
  src = inputs.self + /doc/plutus-core-spec;
}
