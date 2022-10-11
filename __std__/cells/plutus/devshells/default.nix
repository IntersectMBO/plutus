{ inputs, cell }@block:

rec {
  plutus-shell = import ./plutus-shell.nix block;

  # TODO(std)
  # profied-plutus-shell = import ./profiled-plutus-shell.nix block;

  default = plutus-shell;
}
