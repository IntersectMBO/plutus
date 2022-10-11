{ inputs, cell }:

self: super: {

  rPackages = super.rPackages.override {
    overrides = ({
      hexbin = super.rPackages.hexbin.overrideDerivation (attrs: {
        nativeBuildInputs = attrs.nativeBuildInputs ++ [ super.libiconv ];
        buildInputs = attrs.buildInputs ++ [ super.libiconv ];
      });
    });
  };

  # haskell inline-r package fails to compile with more recent version of R:
  # https://github.com/tweag/HaskellR/issues/374
  R = super.R.overrideAttrs (oldAttrs: rec {
    version = "4.1.3";
    src = self.fetchurl {
      url = "https://cran.r-project.org/src/base/R-4/R-${version}.tar.gz";
      sha256 = "sha256-Ff9bMzxhCUBgsqUunB2OxVzELdAp45yiKr2qkJUm/tY=";
    };
    # TODO(std) see if this is still needed
    # Backport https://github.com/NixOS/nixpkgs/pull/99570
    prePatch = super.lib.optionalString super.stdenv.isDarwin ''
      substituteInPlace configure --replace \
        "-install_name libRblas.dylib" "-install_name $out/lib/R/lib/libRblas.dylib"
      substituteInPlace configure --replace \
        "-install_name libRlapack.dylib" "-install_name $out/lib/R/lib/libRlapack.dylib"
      substituteInPlace configure --replace \
        "-install_name libR.dylib" "-install_name $out/lib/R/lib/libR.dylib"
    '';
    # Only need the first patch for 4.1.3:
    patches = [ (builtins.head oldAttrs.patches) ];
  });

}
