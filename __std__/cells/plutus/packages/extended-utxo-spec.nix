{ inputs, cell }:

cell.library.build-latex-doc {
  name = "extended-utxo-spec";
  src = inputs.self + /extended-utxo-spec;
  description = "Extended UTXO specification";
}
