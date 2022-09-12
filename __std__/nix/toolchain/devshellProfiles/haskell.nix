{ inputs, cell }:

_: {

  imports = [
    cell.devshellProfiles.common
  ];

  packages = [
    cell.packages.cabal-install
    cell.packages.cardano-repo-tool
    cell.packages.fix-png-optimization
    cell.packages.fix-stylish-haskell
    cell.packages.fix-cabal-fmt
    cell.packages.haskell-language-server
    cell.packages.hie-bios
    cell.packages.hlint
    cell.packages.stylish-haskell
    cell.packages.nix-flakes-alias
    cell.packages.cabal-fmt
    cell.packages.nixpkgs-fmt

    # TODO(std) check if this is used
    inputs.nixpkgs.ghcid

    # TODO(std) move these 3 into devops shell or script when we have one
    inputs.nixpkgs.awscli2
    inputs.nixpkgs.bzip2
    inputs.nixpkgs.cacert
  ]
  ++ inputs.nixpkgs.lib.optionals (!inputs.nixpkgs.stdenv.isDarwin)
    [
      # TODO(std) uncomment once we have overlayed R and R-packages
      # cell.packages.r-packages.plotly
      # cell.packages.r-lang
    ];
}
