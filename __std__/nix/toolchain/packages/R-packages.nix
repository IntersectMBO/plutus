{ inputs, cell }:

cell.packages.todo-derivation

# TODO(std) !!! this would break the one-derivation-per-file rule, as it's an attrs 
# Figure out a way to deal with this as soon as this derivation is needed.

# let pkgs = inputs.nixpkgs; in

# pkgs.rPackages.override {
#   overrides = ({
#     hexbin = pkgs.rPackages.hexbin.overrideDerivation (attrs: {
#       nativeBuildInputs = attrs.nativeBuildInputs ++ [ pkgs.libiconv ];
#       buildInputs = attrs.buildInputs ++ [ pkgs.libiconv ];
#     });
#   });
# }
