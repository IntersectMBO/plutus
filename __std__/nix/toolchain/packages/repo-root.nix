{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {
  name = "repo-root";
  text = "git rev-parse --show-toplevel";
  runtimeInputs = [ inputs.nixpkgs.git ];
}
