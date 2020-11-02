{ nixpkgs ? <nixpkgs> }:
let
  pkgs = import
    (builtins.fetchTarball {
      name = "nixos-20.03-2020-05-09";
      url = https://github.com/nixos/nixpkgs/archive/d6c1b566b770cf4cf0c6d4a693da6bdf28c2c3b0.tar.gz;
      sha256 = "00vm9shmpywx9dzaj0c7vap1ldimdsr7lw2n8p70qza87nmp9dai";
    })
    { };
  runtimeGhc = pkgs.haskell.packages.ghc883.ghcWithPackages (ps: with ps; [ zlib ]);
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
