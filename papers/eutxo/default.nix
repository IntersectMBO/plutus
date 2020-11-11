{ buildLatexDoc }:

buildLatexDoc {
  name = "eutxo";
  description = "eutxo";
  src = ./.;
  texFiles = [ "eutxo.tex" ];
}
