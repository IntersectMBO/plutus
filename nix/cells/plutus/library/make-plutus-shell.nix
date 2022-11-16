{ inputs, cell }:
{ compiler-nix-name ? cell.library.ghc-compiler-nix-name }:

let
  inherit (cell.library) pkgs haskell-nix;

  plutus-project = cell.library.make-plutus-project { inherit compiler-nix-name; };

  plutus-devshell = haskell-nix.haskellLib.devshellFor plutus-project.shell;
in

inputs.std.lib.dev.mkShell {

  name = "plutus-shell";

  imports = [ plutus-devshell ];

  commands = [
    {
      package = cell.packages.scriv;
      category = "general commands";
      help = "Manage changelogs";
    }
    {
      package = cell.packages.fix-png-optimization;
      category = "general commands";
      help = "Fix all PNG files in-place";
    }
    {
      package = pkgs.shellcheck;
      category = "general commands";
      help = "Shell file checker";
    }
    {
      package = pkgs.editorconfig-checker;
      category = "general commands";
      help = "Checker for editorconfig conformance";
    }
    {
      package = pkgs.R;
      category = "general commands";
      help = "Statistical modelling tool";
    }

    {
      package = cell.packages.fix-cabal-fmt;
      category = "haskell";
      help = "Format all cabal files in-place";
    }
    {
      package = cell.packages.fix-stylish-haskell;
      category = "haskell";
      help = "Run stylish-haskell on all haskell files in-place";
    }
    {
      package = cell.packages.cabal-install;
      name = "cabal";
      category = "haskell";
      help = "Haskell build tool";
    }
    {
      package = cell.packages.haskell-language-server;
      name = "haskell-language-server";
      category = "haskell";
      help = "Haskell Language Server";
    }
    {
      package = cell.packages.hlint;
      name = "hlint";
      category = "haskell";
      help = "Haskell linting tool";
    }
    {
      package = cell.packages.stylish-haskell;
      name = "stylish-haskell";
      category = "haskell";
      help = "Haskell code formatter";
    }
    {
      package = cell.packages.cabal-fmt;
      name = "cabal-fmt";
      category = "haskell";
      help = "Cabal file formatter";
    }
    {
      package = cell.packages.agda-with-stdlib;
      name = "agda";
      category = "haskell";
      help = "Agda and its standard library";
    }

    {
      package = cell.packages.sphinx-build-readthedocs-site;
      category = "docs";
      help = "Build the docs locally in doc/read-the-docs-site/_build";
    }
    {
      package = cell.packages.sphinx-autobuild-readthedocs-site;
      category = "docs";
      help = "Start the autobuild server on localhost:8000";
    }
    {
      package = cell.packages.serve-readthedocs-site;
      category = "docs";
      help = "nix build and serve the doc site on localhost:8002";
    }

    {
      package = cell.packages.nixpkgs-fmt;
      category = "nix";
      help = "Nix code formatter";
    }
    {
      # tullia input isn't de-systemized for some reason
      package = inputs.tullia.packages.${pkgs.system}.tullia;
      category = "nix";
      help = "Tools for working with CI tasks";
    }
    {
      package = cell.packages.check-the-flake;
      category = "nix";
      help = "For nix maintainers: build everything in the flake";
    }
  ];

  packages = [
    # Only occasionally useful, not worth calling out as a command
    cell.packages.hie-bios
    # Provides sphinx-build and other things, unclear how to represent it as a command
    cell.packages.sphinx-toolchain
    # R environment
    cell.library.r-with-packages

    # Misc  useful stuff, could make these commands but there's a lot already
    pkgs.editorconfig-core-c
    pkgs.jq
    pkgs.pre-commit
    pkgs.yq
    pkgs.gnused
    pkgs.awscli2
    pkgs.bzip2

    # Needed to make building things work, not for commands
    pkgs.zlib
    pkgs.cacert
    pkgs.pkg-config # TODO(std) Keep an eye on https://github.com/input-output-hk/plutus/pull/4906
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
