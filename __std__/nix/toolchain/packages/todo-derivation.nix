{ inputs, cell }:

# TODO(std) remove this once standardization is 100% completed
inputs.nixpkgs.writeShellApplication {
  name = "TODO";
  text = "echo TODO";
}
