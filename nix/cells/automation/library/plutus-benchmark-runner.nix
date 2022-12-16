{ cell, inputs }:

{ PR_NUMBER, BENCHMARK_NAME, GITHUB_TOKEN }:

let
  inherit (inputs.cells.plutus.library) pkgs;
in

pkgs.writeShellApplication {
  name = "plutus-benchmark-runner";
  runtimeInputs = [
    pkgs.nix
    pkgs.git
    pkgs.jq
    pkgs.curl
    pkgs.bash
    pkgs.gawk
    pkgs.coreutils
  ];
  text = ''
    export PR_NUMBER="${PR_NUMBER}"
    export BENCHMARK_NAME="${BENCHMARK_NAME}"
    export GITHUB_TOKEN="${GITHUB_TOKEN}"
    ${./plutus-benchmark-runner.sh}
  '';
}
