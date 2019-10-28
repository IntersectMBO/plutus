{ mkDerivation, base, bytestring, Cabal, cryptonite, directory
, ieee754, language-plutus-core, memory, optparse-applicative
, plutus-exe, process, stdenv, text
}:
mkDerivation {
  pname = "plc-agda";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    base bytestring cryptonite ieee754 language-plutus-core memory
    optparse-applicative text
  ];
  testHaskellDepends = [
    base bytestring Cabal cryptonite directory ieee754
    language-plutus-core memory optparse-applicative process text
  ];
  testToolDepends = [ plutus-exe ];
  enableLibraryProfiling = false;
  enableExecutableProfiling = false;
  homepage = "https://github.com/input-output-hk/plutus";
  description = "Command line tool for running plutus core programs";
  license = stdenv.lib.licenses.asl20;
}
