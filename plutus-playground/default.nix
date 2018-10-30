{
  nixpkgs ? builtins.fetchTarball "https://releases.nixos.org/nixos/18.09/nixos-18.09.1023.06fb0253afa/nixexprs.tar.xz"
}:

with (import nixpkgs {});
{
  inherit (callPackage ./plutus-playground-server {}) plutus-playground-server;
  inherit (callPackage ./plutus-playground-client {}) plutus-playground-client;
}
