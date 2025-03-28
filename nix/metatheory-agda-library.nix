{ self, pkgs, lib }:

pkgs.stdenv.mkDerivation {
  pname = "plutus-metatheory-agda-library";
  src = lib.cleanSource (self + /plutus-metatheory);
  nativeBuildInputs = [ pkgs.gnutar ];
  buildPhase = "#";
  installPhase = ''
    mkdir -p $out
    tar -czvf $out/source.tar.gz .
  '';
}
