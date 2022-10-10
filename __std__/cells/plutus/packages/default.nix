{ inputs, cell }@block:
{
  ghc = import ./ghc.nix block;

  agda-with-stdlib = import ./agda-with-stdlib.nix block;
}
