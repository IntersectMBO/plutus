{ haddock-combine, haskell, haskell-nix, writeTextFile }:
let
  toHaddock = haskell-nix.haskellLib.collectComponents' "library" haskell.projectPackagesAllHaddock;
in
haddock-combine {
  hspkgs = builtins.attrValues toHaddock;
  prologue = writeTextFile {
    name = "prologue";
    text = ''
      = Combined documentation for all the public Plutus libraries

      == Handy module entrypoints

        * "PlutusTx": Compiling Haskell to PLC (Plutus Core; on-chain code).
        * "PlutusTx.Prelude": Haskell prelude replacement compatible with PLC.
        * "Plutus.Contract": Writing Plutus apps (off-chain code).
        * "Ledger.Constraints": Constructing and validating Plutus
           transactions. Built on "PlutusTx" and 
           "Plutus.Contract".
        * "Ledger.Typed.Scripts": A type-safe interface for spending and
           producing script outputs. Built on "PlutusTx".
        * "Plutus.Trace.Emulator": Testing Plutus contracts in the emulator.
    '';
  };
}
