{ inputs, cell }:

cell.library.build-latex-doc {
  name = "lazy-machine-notes";
  src = inputs.self + /doc/notes/fomega/lazy-machine;
  texFiles = [ "lazy-plutus-core.tex" ];
  description = "lazy machine discussion";
}
