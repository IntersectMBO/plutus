{ inputs, cell }:

# TODO(std) Remove this patch once the PR makes it into a hackage release.
# See https://github.com/phadej/cabal-fmt/pull/68
let
  project = cell.library.haskell-nix.cabalProject' {

    src = cell.library.pkgs.fetchgit {
      url = "https://github.com/zeme-iohk/cabal-fmt.git";
      rev = "22ee9ffcad6735a8b913fbc211816a55e67a9205";
      sha256 = "sha256-+1pGc3agcAeOhQxe3zOZbx/z2++5pzdSoVlfdl1CBvQ=";
    };

    # Cabal is a boot library, so haskell.nix would normally use the one coming
    # from the compiler-nix-name (currently 3.2). However cabal-fmt depends on
    # Cabal library version 3.6, hence we add this line.
    modules = [{ reinstallableLibGhc = true; }];

    # Doesn't build with 9.2.4
    compiler-nix-name = "ghc8107";
  };
in
project.hsPkgs.cabal-fmt.components.exes.cabal-fmt
