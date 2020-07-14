{ packageSet ? import ./default.nix { rev = "in-nix-shell"; }
}:
with packageSet;
let
  pyEnv = pkgs.python3.withPackages (ps: [ packageSet.sphinxcontrib-haddock.sphinxcontrib-domaintools ps.sphinx ps.sphinx_rtd_theme ]);
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
    # Take cabal from nixpkgs for now, see below
    pkgs.cabal-install

    pyEnv

    # Deployment tools
    pkgs.terraform_0_11
    pkgs.awscli
    pkgs.aws_shell

    # Extra dev packages acquired from elsewhere
    # FIXME: Can't use this cabal until https://github.com/input-output-hk/haskell.nix/issues/422 is fixed
    #dev.packages.cabal-install
    dev.packages.hlint
    dev.packages.stylish-haskell
    dev.packages.haskell-language-server
    dev.packages.hie-bios
    dev.packages.purty
    dev.packages.purs
    dev.packages.spago
    pkgs.stack
    dev.scripts.fixStylishHaskell
    dev.scripts.fixPurty
    dev.scripts.updateClientDeps
    pkgs.python3 # for @reactormonk who's running a python web server
  ] ++ (pkgs.stdenv.lib.optionals (!pkgs.stdenv.isDarwin) [
    # This breaks compilation of R on macOS. The latest version of R
    # does compile, so we can remove it when we upgrade to 20.09.
    pkgs.rPackages.plotly # for generating R plots locally
  ]);
}
