{ inputs, cell }:

# TODO(std) Remove this patch once the PR makes it into a hackage release.
# See https://github.com/phadej/cabal-fmt/pull/68
let
  project = cell.library.haskell-nix.cabalProject' {

    src = cell.library.pkgs.fetchgit {
      url = "https://github.com/zeme-iohk/cabal-fmt.git";
      rev = "0940d6afe980e32a1c6470464380fb48286576b1";
      sha256 = "sha256-800i8vsbyZgvIKJqUJ6OtWcz/G6jak4nVAqA9T3aaPk=";
    };

    # Cabal is a boot library, so haskell.nix would normally use the one coming
    # from the compiler-nix-name (currently 3.2). However cabal-fmt depends on
    # Cabal library version 3.6, hence we add this line.
    modules = [{ reinstallableLibGhc = true; }];

    # Doesn't build with 9.2.4
    compiler-nix-name = "ghc8107";

    index-state = cell.library.cabal-project-index-state;
  };
in
project.hsPkgs.cabal-fmt.components.exes.cabal-fmt
