{ packageSet ? import ./default.nix { rev = "in-nix-shell"; inherit sourcesOverride checkMaterialization useCabalProject; }
, sourcesOverride ? {}
, checkMaterialization ? false
, useCaseShell ? false
, useCabalProject ? useCaseShell
}:
with packageSet; haskell.packages.shellFor ({
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

    # Deployment tools
    pkgs.terraform_0_11
    pkgs.awscli
    pkgs.aws_shell

    dev.packages.cabal
    dev.packages.hlint
    dev.packages.stylish-haskell
    dev.packages.ghcide
    dev.packages.purty
    dev.packages.purs
    dev.packages.spago
    pkgs.stack
  ];
} // pkgs.lib.optionalAttrs useCaseShell {
  packages = ps: with ps; [ plutus-use-cases ];
#  additional = ps: with ps; [ plutus-use-cases ];
})
