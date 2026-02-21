# editorconfig-checker-disable-file

{ inputs, pkgs, lib, project, agda-tools, metatheory, r-with-packages, ghc, mkFourmolu }:

let

  # Toolchain versions used in dev shells. Consumed by `project.shellFor`.
  all-tools = rec {
    "ghc96".cabal = project.projectVariants.ghc96.tool "cabal" "3.12.1.0";
    "ghc96".cabal-fmt = project.projectVariants.ghc96.tool "cabal-fmt" "latest";
    "ghc96".haskell-language-server = project.projectVariants.ghc96.tool "haskell-language-server" "latest";
    "ghc96".stylish-haskell = project.projectVariants.ghc96.tool "stylish-haskell" "latest";
    "ghc96".fourmolu = mkFourmolu ghc;
    "ghc96".hlint = project.projectVariants.ghc96.tool "hlint" "3.8";

    "ghc912".cabal = project.projectVariants.ghc912.tool "cabal" "latest";
    "ghc912".cabal-fmt = project.projectVariants.ghc96.tool "cabal-fmt" "latest"; # cabal-fmt not buildable with ghc9122
    "ghc912".haskell-language-server = project.projectVariants.ghc912.tool "haskell-language-server" "latest";
    "ghc912".stylish-haskell = project.projectVariants.ghc912.tool "stylish-haskell" "latest";
    "ghc912".fourmolu = mkFourmolu ghc;
    "ghc912".hlint = project.projectVariants.ghc912.tool "hlint" "latest";

    "ghc96-profiled" = ghc96;
    "ghc96-plugin" = ghc96;
  };

  tools = all-tools.${ghc};

  # Pre-commit hooks for the repo. Injects into shell via shellHook.
  pre-commit-check = inputs.pre-commit-hooks.lib.${pkgs.stdenv.hostPlatform.system}.run {
    src = ../.;
    hooks = {
      nixpkgs-fmt = {
        enable = true;
        package = pkgs.nixpkgs-fmt;
      };
      cabal-fmt = {
        enable = true;
        package = tools.cabal-fmt;
      };
      stylish-haskell = {
        enable = false;
        package = tools.stylish-haskell;
        args = [ "--config" ".stylish-haskell.yaml" ];
        excludes = [ "^plutus-metatheory/src/MAlonzo" ];
      };
      fourmolu = {
        enable = true;
        package = tools.fourmolu;
        args = [ "--unsafe" ];
        excludes = [ "^plutus-metatheory/src/MAlonzo" ];
      };
      hlint = {
        enable = false;
        package = tools.hlint;
        args = [ "--hint" ".hlint.yaml" ];
      };
      shellcheck = {
        enable = false;
        package = pkgs.shellcheck;
      };
      prettier = {
        enable = false;
        package = pkgs.prettier;
      };
      editorconfig-checker = {
        enable = true;
        package = pkgs.editorconfig-checker;
      };
      generate-malonzo-code = {
        enable = true;
        entry = "${metatheory.generate-malonzo-code}/bin/generate-malonzo-code";
        files = "^plutus-metatheory/src";
        stages = [ "pre-push" ];
        pass_filenames = false;
      };
    };
  };

  # Add extra Linux-only packages to the dev shell here.
  linux-pkgs = lib.optionals pkgs.hostPlatform.isLinux [
    pkgs.papi
    pkgs.util-linux
  ];

  # Common packages/tools available in all shells.
  common-pkgs = [
    agda-tools.agda
    agda-tools.agda-with-stdlib
    agda-tools.agda-mode

    metatheory.generate-malonzo-code
    metatheory.agda-with-stdlib-and-metatheory

    r-with-packages

    inputs.nixpkgs-2405.legacyPackages.${pkgs.stdenv.hostPlatform.system}.linkchecker
    inputs.nixpkgs-2405.legacyPackages.${pkgs.stdenv.hostPlatform.system}.scriv

    tools.haskell-language-server
    tools.stylish-haskell
    tools.fourmolu
    tools.cabal
    tools.hlint
    tools.cabal-fmt

    pkgs.ghcid
    pkgs.texliveFull
    pkgs.jekyll
    pkgs.plantuml
    pkgs.jq
    pkgs.yq
    pkgs.github-cli
    pkgs.gnused
    pkgs.awscli2
    pkgs.act
    pkgs.bzip2
    pkgs.gawk
    pkgs.fswatch
    pkgs.yarn
    pkgs.zlib
    pkgs.cacert
    pkgs.upx
    pkgs.curl
    pkgs.bash
    pkgs.git
    pkgs.which
    pkgs.nodejs_20
  ];

  # Locale archive setup for glibc hosts. Needed to fix cabal build issues on some hosts.
  locale-archive-hook =
    lib.optionalString (pkgs.stdenv.hostPlatform.libc == "glibc")
      "export LOCALE_ARCHIVE=${pkgs.glibcLocales}/lib/locale/locale-archive";

  # Full developer shell with many tools.
  full-shell = project.projectVariants.${ghc}.shellFor {
    name = "plutus-shell-${ghc}";

    buildInputs = lib.concatLists [
      common-pkgs
      linux-pkgs
      pre-commit-check.enabledPackages
    ];

    withHoogle = true;

    shellHook = ''
      ${pre-commit-check.shellHook}
      ${locale-archive-hook}
      export NIX_AGDA_STDLIB=${agda-tools.NIX_AGDA_STDLIB}
      export PS1="\n\[\033[1;32m\][nix-shell:\w]\$\[\033[0m\] "
      echo -e "\n🤟 Welcome to Plutus 🤟"
    '';
  };


  # Lightweight shell with minimal tools.
  quick-shell = project.projectVariants.${ghc}.shellFor {
    name = "plutus-shell-${ghc}";
    tools = { cabal = "latest"; };
    buildInputs = [
      pkgs.git
    ];
    withHoogle = false;
    shellHook = ''
      ${locale-archive-hook}
      export PS1="\n\[\033[1;32m\][nix-shell:\w]\$\[\033[0m\] "
      echo -e "\n🤟 Welcome to Plutus 🤟"
    '';
  };


  # Select shell by compiler used in the project variant.
  shell = {
    ghc96 = full-shell;
    ghc912 = full-shell;
    ghc96-profiled = quick-shell;
    ghc96-plugin = quick-shell;
  }.${ghc};

in

shell
