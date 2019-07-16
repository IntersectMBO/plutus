{ mkDerivation, base, bytestring, cereal, Cocoa, CoreServices, mtl, stdenv, text, unix }:
  mkDerivation {
    pname = "hfsevents";
    version = "0.1.6";
    sha256 = "74c3f3f3a5e55fff320c352a2d481069ff915860a0ab970864c6a0e6b65d3f05";
    libraryHaskellDepends = [ base bytestring cereal mtl text unix ];
    librarySystemDepends = [ Cocoa ];
    libraryToolDepends = [ CoreServices ];
    doHaddock = false;
    doCheck = false;
    homepage = "http://github.com/luite/hfsevents";
    description = "File/folder watching for OS X";
    license = stdenv.lib.licenses.bsd3;
    platforms = [ "x86_64-darwin" ];
  }