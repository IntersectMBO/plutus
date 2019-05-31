{ stdenv
, pkgs
, fetchurl
, psSrc
, yarn2nix
, pp2nSrc
, haskellPackages
}:

with pkgs;

let
  # node-sass is terrible and we have to get it its binaries otherwise it will try to build them
  nodeSassBinLinux = fetchurl {
    url = "https://github.com/sass/node-sass/releases/download/v4.11.0/linux-x64-57_binding.node";
    sha256 = "1hv63bxf3wsknczg0x4431lfgizwqa1fvlhqblh5j4bw3p8mp3c0";
  };
  nodeSassBinDarwin = fetchurl {
    url = "https://github.com/sass/node-sass/releases/download/v4.11.0/darwin-x64-57_binding.node";
    sha256 = "04m3lpqapsx1nsaz7xr6k0yr64car1447v5gf6x6sfiszmshvjw2";
  };
  webCommon = pkgs.copyPathToStore ../web-common;

  packages = callPackage ./packages.nix {};
  mkCopyHook = import "${pp2nSrc}/nix/mkCopyHook.nix";
  installPackages = builtins.toString (builtins.map (mkCopyHook packages) (builtins.attrValues packages.inputs));

in yarn2nix.mkYarnPackage {
  name = "meadow-client";
  src = ./.;
  packageJSON = ./package.json;
  yarnLock = ./yarn.lock;
  yarnNix = ./yarn.nix;
  nodejs = nodejs-10_x; 

  buildInputs = [ git cacert python2 webCommon ];
  nativeBuildInputs = [ psc-package haskellPackages.purescript ];

  buildPhase = ''
    export HOME=$NIX_BUILD_TOP
    export SASS_BINARY_PATH=${if stdenv.isDarwin then nodeSassBinDarwin else nodeSassBinLinux}

    # mkYarnPackage moves everything into deps/meadow
    cd deps/meadow

    # move everything into its correct place
    cp -R ${psSrc} generated
    cp -R ${webCommon} ../web-common

    # do all the psc-package stuff
    ${installPackages}
    mkdir -p .psc-package/local/.set
    cp ${./packages.json} .psc-package/local/.set/packages.json

    # for some reason, mkYarnPackage creates an empty node_modules in deps/meadow.
    rm -Rf ./node_modules

    # Everything is correctly in the top level node_modules though so we link it
    ln -s ../../node_modules
    
    # We have to use nix patched purs and yarn will look in node_modules/.bin first so we have to delete the bad one
    rm ./node_modules/.bin/purs
    
    # we also need to use the nix installed psc-package so don't do yarn run psc-package
    psc-package install

    yarn --offline run webpack
  '';

  doCheck = true;

  checkPhase = ''
    yarn --offline test
  '';

  distPhase = ''
    true
  '';

  installPhase = ''
    mv dist $out
  '';
}
