{ buildLatexDoc }:

buildLatexDoc {
  name = "utxoma";
  description = "utxoma";
  src = ./.;
  texFiles = [ "utxoma.tex" ];
}
