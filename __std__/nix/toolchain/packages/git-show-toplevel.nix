{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {
  name = "git-show-toplevel";
  text = "git rev-parse --show-toplevel";
  runtimeInputs = [ inputs.nixpkgs.git ];
}