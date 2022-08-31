{ inputs, cell }:

cell.packages.todo-derivation

# cardanoRepoToolProject = haskell-nix.cabalProject' {
#   src = sources.cardano-repo-tool;
#   inherit compiler-nix-name index-state;
#   sha256map = {
#     "https://github.com/input-output-hk/nix-archive"."7dcf21b2af54d0ab267f127b6bd8fa0b31cfa49d" = "0mhw896nfqbd2iwibzymydjlb3yivi9gm0v2g1nrjfdll4f7d8ly"; # editorconfig-checker-disable-line
#   };
# };