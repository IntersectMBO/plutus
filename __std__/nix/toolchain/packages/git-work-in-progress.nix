{ inputs, cell }:

cell.library.pkgs.writeShellApplication {
  name = "wip";
  text = "git add . && git commit -m WIP";
  runtimeInputs = [ cell.library.pkgs.git ];
}
