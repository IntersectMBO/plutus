# editorconfig-checker-disable-file 

{ inputs, cell }:

let

  inherit (inputs.cells.toolchain.library.haskell-nix) haskellLib;

  toHaddock = haskellLib.collectComponents' "library"
    (haskellLib.selectProjectPackages inputs.cells.plutus.library.plutus-project.hsPkgs);

in

inputs.cells.toolchain.library.combine-haddock {

  ghc = inputs.cells.plutus.packages.ghc;

  hspkgs = builtins.attrValues toHaddock;

  prologue = inputs.cells.toolchain.library.pkgs.writeTextFile {
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
