{
  description = "Custom Haskell environment with GHC 8.10.7 and cabal-install 3.8.1.0";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        haskellPackages = pkgs.haskell.packages.ghc8107;
        buildInputs = [
          haskellPackages.ghc
          haskellPackages.cabal-install
          pkgs.git
          pkgs.curl
          pkgs.zlib
          pkgs.pkg-config
          pkgs.libsodium
          pkgs.secp256k1
        ];
        libPath = pkgs.lib.makeLibraryPath buildInputs;
      in {
        devShell = pkgs.mkShell {
          inherit buildInputs;
          shellHook = ''
            export LD_LIBRARY_PATH="${libPath}:$LD_LIBRARY_PATH"
            echo "GHC version: $(ghc --version)"
            echo "Cabal version: $(cabal --version)"
          '';
        };
      });
}
