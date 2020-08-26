# This shell can be used with haskell language server in vscode with the following extensions installed
#   https://marketplace.visualstudio.com/items?itemName=haskell.haskell
#   https://marketplace.visualstudio.com/items?itemName=arrterian.nix-env-selector
# To use this file:
#   Open this directory in VSCode
#   Open commands pallet (Cmd + Shift + P) and type Select environment.
#   Select this file.
#   Reload when prompted to do so by the Nix Environment Selector.
{ sourcesOverride ? {}
, checkMaterialization ? false
, useCabalProject ? true
, compiler-nix-name ? "ghc883"
, packageSet ? import ./default.nix ({ rev = "in-nix-shell"; inherit useCabalProject compiler-nix-name; } // args)
}@args:
with packageSet;
let
  # For Sphinx, and ad-hoc usage
  pyEnv = pkgs.python3.withPackages (ps: [ packageSet.sphinxcontrib-haddock.sphinxcontrib-domaintools ps.sphinx ps.sphinx_rtd_theme ]);
  # Called from Cabal to generate the Haskell source for the metatheory package
  agdaWithStdlib = agdaPackages.agda.withPackages [ agdaPackages.standard-library ];
in haskell.packages.shellFor {
  nativeBuildInputs = [
    # From nixpkgs
    pkgs.ghcid
    pkgs.git
    pkgs.cacert
    pkgs.nodejs
    pkgs.yarn
    pkgs.zlib
    pkgs.z3
    # Broken on 20.03, needs a backport
    # pkgs.sqlite-analyzer
    pkgs.sqlite-interactive

    pkgs.stack

    pyEnv

    agdaWithStdlib

    # Deployment tools
    pkgs.terraform_0_11
    pkgs.awscli
    pkgs.aws_shell

    # Extra dev packages acquired from elsewhere
    dev.packages.cabal-install
    dev.packages.hlint
    dev.packages.stylish-haskell
    dev.packages.haskell-language-server
    dev.packages.ghcide
    dev.packages.hie-bios
    dev.packages.purty
    dev.packages.purs
    dev.packages.spago
    dev.scripts.fixStylishHaskell
    dev.scripts.fixPurty
    dev.scripts.updateClientDeps
  ] ++ (pkgs.stdenv.lib.optionals (!pkgs.stdenv.isDarwin) [
    # This breaks compilation of R on macOS. The latest version of R
    # does compile, so we can remove it when we upgrade to 20.09.
    pkgs.rPackages.plotly # for generating R plots locally
  ]);
  packages = ps: with ps; [ plutus-use-cases ];
}
