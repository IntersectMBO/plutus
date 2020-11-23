{ buildLatexDoc }:

buildLatexDoc {
  name = "eutxoma";
  description = "eutxoma";
  src = ./.;
  texFiles = [ "eutxoma.tex" ];
}
