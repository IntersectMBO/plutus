{ inputs, cell }@block:
{
  ghc = import ./ghc.nix block;

  check-the-flake = import ./check-the-flake.nix block;

  fix-cabal-fmt = import ./fix-cabal-fmt.nix block;

  fix-png-optimization = import ./fix-png-optimization.nix block;

  fix-stylish-haskell = import ./fix-stylish-haskell.nix block;

  agda-with-stdlib = import ./agda-with-stdlib.nix block;

  combined-plutus-haddock = import ./combined-plutus-haddock.nix block;

  cabal-fmt = import ./cabal-fmt.nix block;

  cabal-install = import ./cabal-install.nix block;

  haskell-language-server = import ./haskell-language-server.nix block;

  hie-bios = import ./hie-bios.nix block;

  hlint = import ./hlint.nix block;

  nixpkgs-fmt = import ./nixpkgs-fmt.nix block;

  pre-commit-check = import ./pre-commit-check.nix block;

  stylish-haskell = import ./stylish-haskell.nix block;

  scriv = import ./scriv.nix block;

  repo-root = import ./repo-root.nix block;
}
