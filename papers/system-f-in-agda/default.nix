{ buildLatexDoc }:

buildLatexDoc {
  name = "system-f-in-agda";
  src = ./.;
  description = "system-f in agda";
  texFiles = [ "paper.tex" ];
  withAgda = true;
}
