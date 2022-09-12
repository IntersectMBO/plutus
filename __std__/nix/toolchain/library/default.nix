{ inputs, cell }@organelle:
{
  gitignore-nix = import ./gitignore-nix.nix organelle;

  pre-commit-hooks-nix = import ./pre-commit-hooks-nix.nix organelle;

  haskell-nix = import ./haskell-nix.nix organelle;

  combine-haddock = import ./combine-haddock.nix organelle;

  r-packages = import ./r-packages.nix organelle;
}
