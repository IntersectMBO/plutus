# Beacuse AWS Lambda uses an older version of glibc than nixpkgs, we need to build fully static
# binaries.
#
# Unfortunately we cannot build a haskell static binary if the package uses template haskell.
# This is because haskell uses dynamically linked libraries to run template haskell at compile
# time, however we have passed the `-optl=-static` flag which is passed to all linker invocations
# causing these intermediate dynamically linked libraries to fail linking.
#
# In order to get around this we make sure that the TH code is all in libraries and create
# a single haskell file that does nothing other than import the main function from the library.
# We can then pass the `-optl=-static` flag and statically link this as it does not use TH.
{ pkgs, haskellPackages }:
let
  ghc = haskellPackages.ghcWithPackages (p: [ p.marlowe-symbolic ]);
  main = pkgs.writeText "app.hs"
              ''
              module Main where
              import qualified App
              main = App.main
              '';
  z3 = pkgs.callPackage ../nix/z3.nix { staticbin = true; };
  killallz3 = pkgs.writeScriptBin "killallz3" ''
    kill -9 $(ps aux | grep z3 | grep -v grep | awk '{print $2}')
  '';
in
  pkgs.stdenv.mkDerivation {
    name = "marlowe-symbolic-lambda";
    buildInputs = [ pkgs.zip ];
    unpackPhase = "true";
    buildPhase =
      ''
      mkdir -p $out/bin
      ${ghc}/bin/ghc ${main} -static -threaded -o $out/bin/bootstrap \
                     -optl=-static \
                     -optl=-L${pkgs.ncurses.override { enableStatic = true; }}/lib \
                     -optl=-L${pkgs.zlib.static}/lib \
                     -optl=-L${pkgs.gmp6.override { withStatic = true; }}/lib \
                     -optl=-L${pkgs.libffi.overrideAttrs (old: { dontDisableStatic = true; })}/lib
      '';
    installPhase = ''
      zip -j marlowe-symbolic.zip $out/bin/bootstrap ${z3}/bin/z3 ${killallz3}/bin/killallz3
      mv marlowe-symbolic.zip $out/marlowe-symbolic.zip
    '';
  }

