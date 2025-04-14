{ self, pkgs, lib }:

pkgs.stdenv.mkDerivation {
  name = "metatheory-agda-library";
  src = lib.cleanSource (self + /plutus-metatheory);
  nativeBuildInputs = [ pkgs.gnutar ];
  buildPhase = "#";
  installPhase = ''
    mkdir -p $out plutus-metatheory
    find src -name '*agda*' -exec cp -p --parents -t plutus-metatheory {} \;
    cp plutus-metatheory.agda-lib plutus-metatheory
    tar -czvf $out/plutus-metatheory.tar.gz plutus-metatheory
  '';
}
