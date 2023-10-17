{ inputs, cell }:

cell.library.build-latex-doc {
  name = "eutxoma-paper";
  description = "eutxoma";
  src = inputs.self + /doc/papers/eutxoma;
  texFiles = [ "eutxoma.tex" ];
}
