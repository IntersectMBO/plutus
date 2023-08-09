{ system, ... }:
{
  supportedCompilers = [ "ghc8107" "ghc927" "ghc961" ];


  defaultCompiler = "ghc927";


  enableCombinedHaddock = system == "x86_64-linux";


  projectPackagesWithHaddock = [
    "plutus-core"
    "plutus-tx"
    "plutus-tx-plugin"
    "plutus-ledger-api"
    "quickcheck-contractmodel"
  ];


  combinedHaddockPrologue = ''
    = Combined documentation for all the public Plutus libraries

    == Handy module entrypoints

      * "PlutusTx": Compiling Haskell to PLC (Plutus Core; on-chain code).
      * "PlutusTx.Prelude": Haskell prelude replacement compatible with PLC.
      * "PlutusCore": Programming language in which scripts on the Cardano blockchain are written.
      * "UntypedPlutusCore": On-chain Plutus code.
  '';
}
