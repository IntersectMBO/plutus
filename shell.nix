{ packageSet ? import ./default.nix { rev = "in-nix-shell"; }
}:
with packageSet;
let
  # For Sphinx, and ad-hoc usage
  pyEnv = pkgs.python3.withPackages (ps: [ packageSet.sphinxcontrib-haddock.sphinxcontrib-domaintools ps.sphinx ps.sphinx_rtd_theme ]);
  # Called from Cabal to generate the Haskell source for the metatheory package
  agdaWithStdlib = agdaPackages.agda.withPackages [ agdaPackages.standard-library ];
  # Configure project pre-commit hooks
  pre-commit-check = pkgs.nix-pre-commit-hooks.run {
    src = (pkgs.lib.cleanSource ./.);
    tools = {
      stylish-haskell = dev.packages.stylish-haskell;
      nixpkgs-fmt = pkgs.nixpkgs-fmt;
      shellcheck = pkgs.shellcheck;
    };
    hooks = {
      stylish-haskell.enable = true;
      nixpkgs-fmt = {
        enable = true;
        # Get the hook to respect ignore patterns
        # See https://github.com/cachix/pre-commit-hooks.nix/pull/77
        raw.files = "(\\.nix$)|(\\.ignore$)";
      };
      shellcheck.enable = true;
    };
  };
in
haskell.packages.shellFor {
  nativeBuildInputs = [
    # From nixpkgs
    pkgs.ghcid
    # pre-commit-check needs git here
    pkgs.git
    pkgs.cacert
    pkgs.niv
    pkgs.nodejs
    pkgs.shellcheck
    pkgs.yarn
    pkgs.zlib
    pkgs.z3
    pkgs.nixpkgs-fmt
    # Broken on 20.03, needs a backport
    # pkgs.sqlite-analyzer
    pkgs.sqlite-interactive

    pkgs.stack

    pyEnv

    agdaWithStdlib

    # Deployment tools
    pkgs.terraform_0_12
    pkgs.awscli
    pkgs.aws_shell
    pkgs.pass
    pkgs.yubikey-manager

    # Extra dev packages acquired from elsewhere
    dev.packages.cabal-install
    dev.packages.hlint
    dev.packages.stylish-haskell
    dev.packages.haskell-language-server
    dev.packages.hie-bios
    dev.packages.purty
    dev.packages.purs
    dev.packages.spago
    dev.scripts.fixStylishHaskell
    dev.scripts.fixPurty
    dev.scripts.updateClientDeps
    dev.scripts.updateMetadataSamples
  ] ++ (pkgs.stdenv.lib.optionals (!pkgs.stdenv.isDarwin) [
    # This breaks compilation of R on macOS. The latest version of R
    # does compile, so we can remove it when we upgrade to 20.09.
    pkgs.rPackages.plotly # for generating R plots locally
    pkgs.R
  ]);

  # we have a local passwords store that we use for deployments etc.
  PASSWORD_STORE_DIR = toString ./. + "/secrets";

  shellHook = ''
    ${pre-commit-check.shellHook}
  ''
  # Work around https://github.com/NixOS/nix/issues/3345, which makes
  # tests etc. run single-threaded in a nix-shell.
  # Sets the affinity to cores 0-1000 for $$ (current PID in bash)
  # Only necessary for linux - darwin doesn't even expose thread
  # affinity APIs!
  + pkgs.lib.optionalString pkgs.stdenv.isLinux ''
    ${pkgs.utillinux}/bin/taskset -pc 0-1000 $$
  '';
}
