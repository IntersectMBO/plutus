{ inputs, cell }@organelle:
{
  gitignore-nix = import ./gitignore-nix.nix organelle;

  haskell-nix = import ./haskell-nix.nix organelle;

  join-haddock = import ./join-haddock.nix organelle;
}
