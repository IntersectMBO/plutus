{ nixpkgs ? <nixpkgs> }:
let
  pkgs = import
    (builtins.fetchTarball {
      name = "nixos-20.09";
      url = https://github.com/NixOS/nixpkgs/archive/20.09.tar.gz;
    })
    { };
  runtimeGhc = pkgs.haskell.packages.ghc8102.ghcWithPackages (ps: with ps; [ zlib ]);
in
with pkgs; mkShell {
  buildInputs = [
    runtimeGhc
    cabal-install
    stack
    wget
    curl
    binutils
    git
    vim
    openssl.dev
  ];
}
