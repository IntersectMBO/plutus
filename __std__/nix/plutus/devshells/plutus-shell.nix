{ inputs, cell }:

let
  inherit (inputs.cells.toolchain.library) pkgs;
in

inputs.std.std.lib.mkShell {

  name = "plutus-shell";

  imports = [
    cell.library.plutus-project.devshell
    inputs.cells.toolchain.devshellProfiles.haskell
  ];

  packages = pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [
    pkgs.rPackages.plotly
    pkgs.R
  ];

}
