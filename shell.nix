{ sourcesOverride ? {}
, checkMaterialization ? false
, useCabalProject ? true
, compiler-nix-name ? "ghc883"
}@args:
let
  packageSet = import ./default.nix ({ rev = "in-nix-shell"; inherit useCabalProject compiler-nix-name; } // args);
  pyEnv = packageSet.pkgs.python3.withPackages (ps: [ packageSet.sphinxcontrib-haddock.sphinxcontrib-domaintools ps.sphinx ps.sphinx_rtd_theme ]);
in
with packageSet; haskell.packages.shellFor {
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
}
