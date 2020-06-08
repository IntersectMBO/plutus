{ packageSet ? import ./default.nix { rev = "in-nix-shell"; inherit sourcesOverride checkMaterialization useCabalProject; }
, sourcesOverride ? {}
, checkMaterialization ? false
, useCaseShell ? false  # Set to true for working on plutus scripts.
                        # This will include prebuilt dependencies of plutus-use-cases and
                        # a version of ghcide that works with plutus modules.
, useCabalProject ? useCaseShell  # Chooses between `cabalProject` or `stackProject`
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
    (if useCaseShell
      then dev.packages.ghcide-use-cases
      else dev.packages.ghcide)
    dev.packages.purty
    dev.packages.purs
    dev.packages.spago
    pkgs.stack
  ];
} // pkgs.lib.optionalAttrs useCaseShell {
  packages = ps: with ps; [ plutus-use-cases ];
})
