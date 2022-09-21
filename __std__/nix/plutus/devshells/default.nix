{ inputs, cell }@block:

rec {
  plutus-shell = import ./plutus-shell.nix block;

  default = plutus-shell;
}
