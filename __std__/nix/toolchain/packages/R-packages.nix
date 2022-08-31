{ inputs, cell }:

# TODO(std) this breaks the one-derivation-per-file rule, as it's an attrs

cell.packages.todo-derivation

  # rPackages = super.rPackages.override {
  #   overrides = ({
  #     hexbin = super.rPackages.hexbin.overrideDerivation (attrs: {
  #       nativeBuildInputs = attrs.nativeBuildInputs ++ [ super.libiconv ];
  #       buildInputs = attrs.buildInputs ++ [ super.libiconv ];
  #     });
  #   });
  # };