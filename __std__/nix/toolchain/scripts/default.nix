{ inputs, cell }@organelle:
{
  cabal-fmt-checker = import ./cabal-fmt-checker.nix organelle;

  editorconfig-checker = import ./editorconfig-checker.nix organelle;

  nixpkgs-fmt-checker = import ./nixpkgs-fmt-checker.nix organelle;

  png-optimization-checker = import ./png-optimization-checker.nix organelle;

  shellcheck-checker = import ./shellcheck-checker.nix organelle;

  stylish-haskell-checker = import ./stylish-haskell-checker.nix organelle;
}
