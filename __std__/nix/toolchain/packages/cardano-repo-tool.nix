{ inputs, cell }:

# TODO(std) we need haskell-nix for this
# TODO(std) actually delete this if nothing breaks

let
  project = cell.library.haskell-nix.cabalProject' {

    src = inputs.cardano-repo-tool;

    compiler-nix-name = cell.library.ghc-compiler-nix-name;

    index-state = cell.library.cabal-project-index-state;

    sha256map = {
      "https://github.com/input-output-hk/nix-archive"."7dcf21b2af54d0ab267f127b6bd8fa0b31cfa49d" = "0mhw896nfqbd2iwibzymydjlb3yivi9gm0v2g1nrjfdll4f7d8ly"; # editorconfig-checker-disable-line
    };
  };
in
project.hsPkgs.cardano-repo-tool
