{ inputs, cell }:

cell.library.build-latex-doc {
  name = "cost-model-notes";
  src = inputs.self + /doc/notes/cost-model-notes;
  description = "Notes on cost models";
  texFiles = [ "cost-model-notes.tex" ];
}
