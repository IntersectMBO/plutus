{ inputs, cell }:

cell.packages.todo-derivation

# TODO(std) what is this for?
# nixFlakesAlias = pkgs.runCommand "nix-flakes-alias" { } ''
#   mkdir -p $out/bin
#   ln -sv ${pkgs.nixFlakes}/bin/nix $out/bin/nix-flakes
# '';