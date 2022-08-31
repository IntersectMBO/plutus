{ inputs, cell }:

inputs.std.std.lib.mkShell {
  
  name = "plutus-shell";

  imports = [
    inputs.cells.toolchain.devshellProfiles.haskell
  ];
}
