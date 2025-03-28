{ self, pkgs, lib }:

pkgs.stdenv.mkDerivation {
  name = "metatheory-agda-library";
  src = lib.cleanSource (self + /plutus-metatheory);
  nativeBuildInputs = [ pkgs.gnutar ];
  buildPhase = "#";
  installPhase = ''
    mkdir -p $out
    tar -czvf $out/plutus-metatheory.tar.gz .
  '';
}
