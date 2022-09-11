{ inputs, cell }@organelle:
{
  gitignore-nix = import ./gitignore-nix.nix organelle;

  haskell-nix = import ./haskell-nix.nix organelle;
}
