{ inputs, cell }:

cell.packages.todo-derivation

# TODO(std) !!! this would break the one-derivation-per-file rule, as it's an attrs TODO
# Must figure out a way to deal with this

# let pkgs = inputs.nixpkgs; in

# pkgs.rPackages.override {
#   overrides = ({
#     hexbin = pkgs.rPackages.hexbin.overrideDerivation (attrs: {
#       nativeBuildInputs = attrs.nativeBuildInputs ++ [ pkgs.libiconv ];
#       buildInputs = attrs.buildInputs ++ [ pkgs.libiconv ];
#     });
#   });
# }
