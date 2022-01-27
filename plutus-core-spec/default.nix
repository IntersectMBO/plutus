{ buildLatexDoc }:

buildLatexDoc {
  name = "plutus-core-spec";
  description = "Plutus core specification";
  src = ./.;
  texFiles = [ "plutus-core-specification.tex" ];
}
