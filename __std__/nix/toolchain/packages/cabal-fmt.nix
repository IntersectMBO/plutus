{ inputs, cell }:

# TODO(std) we need haskell-nix for this

# TODO Remove this patch once the PR gets merged upstream.
# See https://github.com/phadej/cabal-fmt/pull/45
let
  project = cell.library.haskell-nix.cabalProject' {

    src = inputs.nixpkgs.fetchgit {
      url = "https://github.com/zeme-iohk/cabal-fmt.git";
      rev = "7b5c9b4fac55aad15a0b33bcd22b40a244bf30af";
      sha256 = "04w1dy83ml7wgm5ay1rd4kiwfmdd9sc2y8bp3l0ja7xwvh4fgkmr";
    };

    # Cabal is a boot library, so haskell.nix would normally use the one coming
    # from the compiler-nix-name (currently 3.2). However cabal-fmt depends on
    # Cabal library version 3.6, hence we add this line.
    modules = [{ reinstallableLibGhc = true; }];

    compiler-nix-name = cell.library.ghc-compiler-nix-name;

    index-state = cell.library.cabal-project-index-state;
  };
in
project.hsPkgs.cabal-fmt
