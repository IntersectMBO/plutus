{ inputs, cell }@block:
{
  cabal-fmt-checker = import ./cabal-fmt-checker.nix block;

  editorconfig-checker = import ./editorconfig-checker.nix block;

  nixpkgs-fmt-checker = import ./nixpkgs-fmt-checker.nix block;

  png-optimization-checker = import ./png-optimization-checker.nix block;

  shellcheck-checker = import ./shellcheck-checker.nix block;

  stylish-haskell-checker = import ./stylish-haskell-checker.nix block;
}
