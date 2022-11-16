{ cell, inputs }:

{ PR_NUMBER, PR_COMMIT_SHA, BENCHMARK_NAME, GITHUB_TOKEN }:

let
  inherit (inputs.cells.plutus.library) pkgs;
in

pkgs.writeShellApplication {
  name = "plutus-benchmark-runner";
  runtimeInputs = [ pkgs.nix pkgs.git pkgs.jq pkgs.curl ];
  text = ''
    PR_NUMBER=${PR_NUMBER} \
    PR_COMMIT_SHA=${PR_COMMIT_SHA} \
    BENCHMARK_NAME=${BENCHMARK_NAME} \
    GITHUB_TOKEN=${GITHUB_TOKEN} \
    ${./plutus-benchmark-runner.sh}
  '';
}
