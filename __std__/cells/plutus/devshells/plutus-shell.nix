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

  commands = [
    {
      package = inputs.cells.toolchain.packages.fix-cabal-fmt;
      category = "plutus";
      help = "Format all cabal files in-place";
    }
    {
      package = inputs.cells.toolchain.packages.fix-png-optimization;
      category = "plutus";
      help = "Fix all PNG files in-place";
    }
    {
      package = inputs.cells.toolchain.packages.fix-stylish-haskell;
      category = "plutus";
      help = "Run stylish-haskell on all haskell files in-place";
    }
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
    pkgs.pkg-config # TODO(std) Keep an eye on https://github.com/input-output-hk/plutus/pull/4906

    pkgs.rPackages.plotly
    pkgs.R
  ];

  env = [
    # This is no longer set automatically as of more recent `haskell.nix` revisions,
    # but is useful for users with LANG settings.
    {
      name = "LOCALE_ARCHIVE";
      value = pkgs.lib.optionalString
        (pkgs.stdenv.hostPlatform.libc == "glibc") "${pkgs.glibcLocales}/lib/locale/locale-archive";
    }
  ];
}
