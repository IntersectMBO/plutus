{ inputs, cell }:

cell.library.build-latex-doc {
  name = "eutxoma-paper";
  description = "eutxoma";
  src = inputs.self + /papers/eutxoma;
  texFiles = [ "eutxoma.tex" ];
}
