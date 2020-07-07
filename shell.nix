{ sourcesOverride ? {}
, checkMaterialization ? false
, useCabalProject ? false
}@args:
let
  packageSet = import ./default.nix ({ rev = "in-nix-shell"; } // args);
  pyEnv = pkgs.python3.withPackages (ps: [ ps.sphinx ps.sphinx_rtd_theme ]);
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
    # Take cabal from nixpkgs for now, see below
    pkgs.cabal-install

    pyEnv

    # Deployment tools
    pkgs.terraform_0_11
    pkgs.awscli
    pkgs.aws_shell

    dev.packages.hlint
    dev.packages.stylish-haskell
    dev.packages.haskell-language-server
    dev.packages.purty
    dev.packages.purs
    dev.packages.spago
    pkgs.stack
    dev.scripts.fixStylishHaskell
    dev.scripts.fixPurty
    dev.scripts.updateClientDeps
  ];
}
