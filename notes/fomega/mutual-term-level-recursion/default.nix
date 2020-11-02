{ pkgs ? import <nixpkgs> { } }:

pkgs.agda.mkDerivation (self: {
  src = pkgs.lib.cleanSource ./.;
  name = "FixN";
  topSourceDirectories = [ "." ];
  everythingFile = "FixN.agda";
  buildDepends = [ pkgs.AgdaStdlib ];
})
