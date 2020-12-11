self: super: {
  rPackages = super.rPackages.override {
    overrides = ({
      hexbin = super.rPackages.hexbin.overrideDerivation (attrs: {
        nativeBuildInputs = attrs.nativeBuildInputs ++ [ super.libiconv ];
        buildInputs = attrs.buildInputs ++ [ super.libiconv ];
      });
    });
  };
  R = super.R.overrideAttrs (oldAttrs: {
    # Backport https://github.com/NixOS/nixpkgs/pull/99570
    prePatch = super.stdenv.lib.optionalString super.stdenv.isDarwin ''
      substituteInPlace configure --replace "-install_name libRblas.dylib" "-install_name $out/lib/R/lib/libRblas.dylib"
      substituteInPlace configure --replace "-install_name libRlapack.dylib" "-install_name $out/lib/R/lib/libRlapack.dylib"
      substituteInPlace configure --replace "-install_name libR.dylib" "-install_name $out/lib/R/lib/libR.dylib"
    '';
  });

}
