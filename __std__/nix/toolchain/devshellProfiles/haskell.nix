{ inputs, cell }:

_: {

  imports = [
    cell.devshellProfiles.common
  ];

  packages = [
    cell.packages.cabal-install
    cell.packages.fix-png-optimization
    cell.packages.fix-stylish-haskell
    cell.packages.fix-cabal-fmt
    cell.packages.haskell-language-server
    cell.packages.hie-bios
    cell.packages.hlint
    cell.packages.stylish-haskell
    cell.packages.cabal-fmt
    cell.packages.nixpkgs-fmt

    # TODO(std) check if this is used
    cell.library.pkgs.ghcid

    cell.library.pkgs.awscli2
    cell.library.pkgs.bzip2
    cell.library.pkgs.cacert
  ];
}
