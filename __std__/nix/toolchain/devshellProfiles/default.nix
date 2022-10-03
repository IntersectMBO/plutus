{ inputs, cell }@block:
{
  common = import ./common.nix block;

  haskell = import ./haskell.nix block;
}
