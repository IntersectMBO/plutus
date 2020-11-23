{ buildLatexDoc }:

buildLatexDoc {
  name = "cost-model-notes";
  src = ./.;
  description = "Notes on cost models";
  texFiles = [ "cost-model-notes.tex" ];
}
