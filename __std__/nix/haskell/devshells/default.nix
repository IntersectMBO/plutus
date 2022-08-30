{ inputs, cell }@organelle:
{
  haskell-shell = import ./haskell-shell.nix organelle;
}