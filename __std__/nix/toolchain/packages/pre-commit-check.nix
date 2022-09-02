{ inputs, cell }:

cell.packages.todo-derivation

# TODO(std) we need stylish-haskell for this

# # Configure project pre-commit hooks
# pre-commit-check = nix-pre-commit-hooks.run {
#   src = (lib.cleanSource ./.);
#   tools = {
#     stylish-haskell = stylish-haskell;
#     nixpkgs-fmt = nixpkgs-fmt;
#     shellcheck = pkgs.shellcheck;
#     cabal-fmt = cabal-fmt;
#   };
#   hooks = {
#     stylish-haskell.enable = true;
#     nixpkgs-fmt = {
#       enable = true;
#       # While nixpkgs-fmt does exclude patterns specified in `.ignore` this
#       # does not appear to work inside the hook. For now we have to thus
#       # maintain excludes here *and* in `./.ignore` and *keep them in sync*.
#       excludes =
#         [
#           ".*nix/pkgs/haskell/materialized.*/.*"
#           ".*/spago-packages.nix$"
#           ".*/packages.nix$"
#         ];
#     };
#     cabal-fmt.enable = true;
#     shellcheck.enable = true;
#     png-optimization = {
#       enable = true;
#       name = "png-optimization";
#       description = "Ensure that PNG files are optimized";
#       entry = "${pkgs.optipng}/bin/optipng";
#       files = "\\.png$";
#     };
#   };
# };
