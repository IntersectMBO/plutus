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
{ pkgs, lib, ghcWithPackages }:
let
  ghc = ghcWithPackages (p: [ p.marlowe-symbolic ]);
  main = pkgs.writeText "app.hs"
    ''
      module Main where
      import qualified Marlowe.Symbolic.Lambda as Lambda
      main = Lambda.main
    '';

  z3 = pkgs.z3.override { staticbin = true; };
  openssl = (pkgs.openssl.override { static = true; }).overrideAttrs (old: {
    # "no-shared" per https://github.com/NixOS/nixpkgs/pull/77542, should be able to
    # get rid of this when we update nixpkgs
    configureFlags = old.configureFlags ++ [ "no-shared" ];
  });
  gmp6 = pkgs.gmp6.override { withStatic = true; };
  zlib = pkgs.zlib.override { static = true; };
  ncurses = pkgs.ncurses.override { enableStatic = true; };
  libffi = pkgs.libffi.overrideAttrs (old: { dontDisableStatic = true; });
  numactl = pkgs.numactl.overrideAttrs (_: { configureFlags = "--enable-static"; });

  killallz3 = pkgs.writeScriptBin "killallz3" ''
    kill -9 $(ps aux | grep z3 | grep -v grep | awk '{print $2}')
  '';
in
pkgs.stdenv.mkDerivation {
  name = "marlowe-symbolic-lambda";
  nativeBuildInputs = [ pkgs.zip ];
  unpackPhase = "true";
  buildPhase =
    ''
      mkdir -p $out/bin
      ${ghc}/bin/${ghc.targetPrefix}ghc ${main} -static -threaded -o $out/bin/bootstrap \
                     -optl=-static \
                     -optl=-L${lib.getLib ncurses}/lib \
                     -optl=-L${lib.getLib zlib}/lib \
                     -optl=-L${lib.getLib gmp6}/lib \
                     -optl=-L${lib.getLib openssl}/lib \
                     -optl=-L${lib.getLib libffi}/lib \
                     -optl=-L${lib.getLib numactl}/lib
    '';
  installPhase = ''
    zip -j marlowe-symbolic.zip $out/bin/bootstrap ${z3}/bin/z3 ${killallz3}/bin/killallz3
    mv marlowe-symbolic.zip $out/marlowe-symbolic.zip
  '';

  # Marlowe lambda builds with musl, and only on linux
  meta.platforms = lib.platforms.linux;
}
