{ inputs, cell }:

cell.library.build-latex-doc {
  name = "utxoma-paper";
  description = "utxoma";
  src = inputs.self + /doc/papers/utxoma;
  texFiles = [ "utxoma.tex" ];
}
