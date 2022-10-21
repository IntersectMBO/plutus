{ inputs, cell }:
{ compiler-nix-name ? inputs.cells.toolchain.library.ghc-compiler-nix-name }:

let
  inherit (cell.library) pkgs;
in

inputs.std.lib.dev.mkShell {

  name = "plutus-shell";

  imports = [
    (cell.library.make-plutus-project { inherit compiler-nix-name; }).devshell
  ];

  commands = [
    {
      package = cell.packages.check-the-flake;
      category = "general commands";
      help = "For nix maintainers: build everything in the flake";
    }
    {
      package = cell.packages.fix-cabal-fmt;
      category = "plutus";
      help = "Format all cabal files in-place";
    }
    {
      package = cell.packages.fix-png-optimization;
      category = "plutus";
      help = "Fix all PNG files in-place";
    }
    {
      package = cell.packages.fix-stylish-haskell;
      category = "plutus";
      help = "Run stylish-haskell on all haskell files in-place";
    }
    {
      package = cell.packages.sphinx-build-readthedocs-site;
      category = "docs";
      help = "Build the docs locally with output in doc/_build";
    }
    {
      package = cell.packages.sphinx-autobuild-readthedocs-site;
      category = "docs";
      help = "Start the autobuild server with output in doc/_build";
    }
    {
      package = cell.packages.serve-readthedocs-site;
      category = "docs";
      help = "nix build and serve the doc site on port 3000";
    }
  ];

  packages = [
    cell.packages.sphinx-toolchain
    cell.packages.cabal-install
    cell.packages.haskell-language-server
    cell.packages.hie-bios
    cell.packages.hlint
    cell.packages.stylish-haskell
    cell.packages.cabal-fmt
    cell.packages.nixpkgs-fmt

    # tullia input isn't de-systemized for some reason
    inputs.tullia.packages.${pkgs.system}.tullia

    pkgs.editorconfig-core-c
    pkgs.editorconfig-checker
    pkgs.jq
    pkgs.pre-commit
    pkgs.shellcheck
    pkgs.yq
    pkgs.zlib
    pkgs.ghcid
    pkgs.gnused
    pkgs.awscli2
    pkgs.bzip2
    pkgs.cacert
    pkgs.pkg-config # TODO(std) Keep an eye on https://github.com/input-output-hk/plutus/pull/4906

    pkgs.rPackages.plotly
    pkgs.R
  ];

  devshell.startup."pre-commit-check".text = cell.packages.pre-commit-check.shellHook;

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
