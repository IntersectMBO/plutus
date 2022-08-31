{ inputs, cell }:

let pkgs = inputs.nixpkgs; in

pkgs.R.overrideAttrs (oldAttrs: {

  # Backport https://github.com/NixOS/nixpkgs/pull/99570
  prePatch = pkgs.lib.optionalString pkgs.stdenv.isDarwin ''
    substituteInPlace configure --replace \
      "-install_name libRblas.dylib" "-install_name $out/lib/R/lib/libRblas.dylib"
    substituteInPlace configure --replace \
      "-install_name libRlapack.dylib" "-install_name $out/lib/R/lib/libRlapack.dylib"
    substituteInPlace configure --replace \
      "-install_name libR.dylib" "-install_name $out/lib/R/lib/libR.dylib"
  '';
})
