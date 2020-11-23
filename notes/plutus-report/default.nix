{ buildLatexDoc }:

buildLatexDoc {
  name = "plutus";
  src = ./.;
  texFiles = [ "plutus.tex" ];
  description = "plutus report";
}
