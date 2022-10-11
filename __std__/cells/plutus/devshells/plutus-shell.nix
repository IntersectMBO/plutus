{ inputs, cell }:

let
  inherit (inputs.cells.toolchain.library) pkgs;
in

inputs.std.lib.dev.mkShell {

  name = "plutus-shell";

  imports = [
    cell.library.plutus-project.devshell

    inputs.cells.toolchain.devshellProfiles.common
  ];

  packages = [

    inputs.cells.toolchain.packages.cabal-install
    inputs.cells.toolchain.packages.fix-png-optimization
    inputs.cells.toolchain.packages.fix-stylish-haskell
    inputs.cells.toolchain.packages.fix-cabal-fmt
    inputs.cells.toolchain.packages.haskell-language-server
    inputs.cells.toolchain.packages.hie-bios
    inputs.cells.toolchain.packages.hlint
    inputs.cells.toolchain.packages.stylish-haskell
    inputs.cells.toolchain.packages.cabal-fmt
    inputs.cells.toolchain.packages.nixpkgs-fmt

    pkgs.ghcid
    pkgs.awscli2
    pkgs.bzip2
    pkgs.cacert

  ] ++ pkgs.lib.optionals (!pkgs.stdenv.isDarwin) [
    pkgs.rPackages.plotly
    pkgs.R
  ];

}
