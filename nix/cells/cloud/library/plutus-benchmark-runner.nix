{ cell, inputs }:

{ PR_NUMBER, PR_COMMIT_SHA, BENCHMARK_NAME }:

let
  inherit (inputs.cells.plutus.library) pkgs;
in

pkgs.writeShellApplication {
  name = "plutus-benchmark-runner";
  runtimeInputs = [ pkgs.nix pkgs.git pkgs.jq pkgs.curl ];
  text = "${./plutus-benchmark-runner.sh} ${PR_NUMBER} ${PR_COMMIT_SHA} ${BENCHMARK_NAME}";
}
