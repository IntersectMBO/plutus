{ inputs, cell }:

# TODO(std) remove this once standardization is 100% completed
cell.library.pkgs.writeShellApplication {
  name = "TODO";
  text = "echo TODO";
}
