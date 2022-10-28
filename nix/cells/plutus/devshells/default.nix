{ inputs, cell }@block:

rec {
  plutus-shell = import ./plutus-shell.nix block;

  plutus-shell-924 = import ./plutus-shell-924.nix block;

  # TODO(std)
  # profiled-plutus-shell = import ./profiled-plutus-shell.nix block;

  default = plutus-shell;
}
