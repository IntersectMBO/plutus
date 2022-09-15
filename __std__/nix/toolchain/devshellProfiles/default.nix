{ inputs, cell }@organelle:
{
  common = import ./common.nix organelle;

  haskell = import ./haskell.nix organelle;
}
