{ inputs, cell }:

cell.library.build-latex-doc {
  name = "eutxo-paper";
  description = "eutxo";
  src = inputs.self + /papers/eutxo;
  texFiles = [ "eutxo.tex" ];
}