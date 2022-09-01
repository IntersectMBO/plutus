{ inputs, cell }:

cell.packages.todo-derivation

# let src = inputs.cells.toolchain.packages.gitignore-nix.gitignoreSource inputs.self; in

# inputs.nixpkgs.writeShellApplication {

#   name = "editorconfig-checker";

#   runtimeInputs = [
#     inputs.nixpkgs.editorconfig-checker
#   ];

#   text = ''
#     mkdir -p "$out/nix-support"

#     set -e
#     # changing to the directory and then running it gives better output than
#     # passing the directory to check, since file names are shorter
#     cd $src
#     editorconfig-checker 2>&1 | tee "$out/nix-support/editorconfig-checker.log"

#     if [ $? -ne 0 ]; then
#       echo "*** editorconfig-checker found files that don't match the configuration"
#       exit 1
#     fi
#   '';
# }
