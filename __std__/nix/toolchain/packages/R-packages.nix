{ inputs, cell }:

cell.packages.todo-derivation

# TODO(std) we want this to be an overlay

# let pkgs = inputs.nixpkgs; in

# pkgs.rPackages.override {
#   overrides = ({
#     hexbin = pkgs.rPackages.hexbin.overrideDerivation (attrs: {
#       nativeBuildInputs = attrs.nativeBuildInputs ++ [ pkgs.libiconv ];
#       buildInputs = attrs.buildInputs ++ [ pkgs.libiconv ];
#     });
#   });
# }
