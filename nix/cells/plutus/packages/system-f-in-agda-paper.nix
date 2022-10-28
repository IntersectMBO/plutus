{ inputs, cell }:

cell.library.build-latex-doc {
  name = "system-f-in-agda-paper";
  src = inputs.self + /doc/papers/system-f-in-agda;
  description = "system-f in agda";
  texFiles = [ "paper.tex" ];
  withAgda = true;
  agdaFile = "paper.lagda";
}
