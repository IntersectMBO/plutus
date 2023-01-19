{ inputs, cell }:

inputs.cells.toolchain.pkgs.writeShellApplication {
  name = "repo-root";
  text = "git rev-parse --show-toplevel";
  runtimeInputs = [ inputs.cells.toolchain.pkgs.git ];
}
