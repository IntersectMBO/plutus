{ mkDerivation, base, bytestring, cryptonite, ieee754
, language-plutus-core, memory, stdenv, text
}:
mkDerivation {
  pname = "plc-agda";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    base bytestring cryptonite ieee754 language-plutus-core memory text
  ];
  homepage = "https://github.com/input-output-hk/plutus";
  description = "Command line tool for running plutus core programs";
  license = stdenv.lib.licenses.asl20;
}
