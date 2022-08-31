{ inputs, cell }:

cell.packages.todo-derivation


# { runCommand, editorconfig-checker, src }:

# # Runs `editorconfig-checker` on ${src}. If there are errors,
# # they are written to `$out/nix-support/hydra-build-products`
# runCommand "editorconfig-checker"
# {
#   buildInputs = [ editorconfig-checker ];
# } ''
#   mkdir -p "$out/nix-support"

#   # changing to the directory and then running it gives better output than
#   # passing the directory to check, since file names are shorter
#   cd ${src}
#   editorconfig-checker 2>&1 | tee "$out/nix-support/editorconfig-checker.log"

#   if [ $? -ne 0 ]; then
#     echo "*** editorconfig-checker found files that don't match the configuration"
#     exit 1
#   fi
# ''
