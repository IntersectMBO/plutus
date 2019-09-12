{ nixpkgs ? <nixpkgs> }:
let
  pkgs = import (builtins.fetchTarball {
    name = "nixos-unstable-2018-12-08";
    url = https://github.com/nixos/nixpkgs/archive/4557b9f1f50aa813ae673fe6fcd30ca872968947.tar.gz;
    sha256 = "0cam48cn042axcik9vqxsqjc2hwyb2grjbjxacsn4w0y1zk6k6l2";
    }) {
      config = {
        packageOverrides = pkgs: rec {
          vscode = pkgs.vscode.overrideDerivation (old: {
            nativeBuildInputs = [ pkgs.makeWrapper ];
            postFixup = ''
              wrapProgram $out/bin/code --prefix PATH : ${pkgs.lib.makeBinPath [hies pkgs.cabal-install]}
            '';
          });
        };
      };
    };
  all-hies = import (fetchTarball "https://github.com/infinisil/all-hies/tarball/master") {};
  # Install stable HIE for GHC 8.6.5
  hies = all-hies.selection { selector = p: { inherit (p) ghc865; }; };
in
with pkgs; mkShell {
  buildInputs = [
    ghc 
    openssl
    hies
    cabal-install
    vscode
  ];
}
