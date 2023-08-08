{ inputs, cell }@block:

rec {
  plutus-shell-810 = import ./plutus-shell-810.nix block;

  plutus-shell-92 = import ./plutus-shell-92.nix block;

  plutus-shell-96 = import ./plutus-shell-96.nix block;

  # TODO(std)
  # profiled-plutus-shell = import ./profiled-plutus-shell.nix block;

  default = plutus-shell-92;
}
