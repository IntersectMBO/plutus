{ inputs, cell }:

cell.library.pkgs.writeShellApplication {
  name = "repo-root";
  text = "git rev-parse --show-toplevel";
  runtimeInputs = [ cell.library.pkgs.git ];
}
