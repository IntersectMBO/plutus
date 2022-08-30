{ inputs, cell }:

cell.library.build-latex-doc {
  name = "plutus-report";
  description = "plutus report";
  src = inputs.self + /plutus-core-spec; 
}
