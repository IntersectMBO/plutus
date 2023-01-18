{ inputs, cell }@block:

rec {
  plutus-shell-8107 = import ./plutus-shell-8107.nix block;

  plutus-shell-924 = import ./plutus-shell-924.nix block;

  # TODO(std)
  # profiled-plutus-shell = import ./profiled-plutus-shell.nix block;

  default = plutus-shell-924;
}
