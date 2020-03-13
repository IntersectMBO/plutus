{ packageSet ? import ./default.nix { rev = "in-nix-shell"; }
}:
with packageSet; haskell.packages.shellFor {
  nativeBuildInputs = [
    # From nixpkgs
    pkgs.ghcid
    pkgs.git
    pkgs.cacert
    pkgs.yarn
    pkgs.zlib
    pkgs.z3
    pkgs.sqlite-analyzer
    pkgs.sqlite-interactive

    # Extra dev packages acquired from elsewhere
    dev.packages.cabal-install
    dev.packages.hlint
    dev.packages.stylish-haskell
    dev.packages.purty
    dev.packages.purs
    dev.packages.spago
  ];
}
