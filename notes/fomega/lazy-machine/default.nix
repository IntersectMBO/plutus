{ buildLatexDoc }:

buildLatexDoc {
  name = "lazy-machine";
  src = ./.;
  texFiles = [ "lazy-plutus-core.tex" ];
  description = "lazy machine discussion";
}
