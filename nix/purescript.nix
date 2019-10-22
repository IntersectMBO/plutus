{ stdenv
, pkgs
, fetchurl
, psSrc
, easyPS
, yarn2nix
, nodejsHeaders
, src
, webCommonPath
, packages
, spagoPackages
, name
, packageJSON
, yarnLock
, yarnNix
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
  webCommon = pkgs.copyPathToStore webCommonPath;

  packagesJson = "${src}/packages.json";

  # remove any files that have appeared in local builds
  cleanSrcs = builtins.filterSource (path: type: !(pkgs.lib.elem (baseNameOf path)
                                                  [".spago" ".spago2nix" "generated" "generated-docs" "output" "dist"]))
                                                  src;

in yarn2nix.mkYarnPackage {
  inherit name packageJSON yarnLock yarnNix;
  src = cleanSrcs;
  nodejs = nodejs-10_x;

  pkgConfig = {
    "libxmljs" = {
      buildInputs = [ nodejs-10_x nodePackages_10_x.node-gyp python2 ];
      postInstall = ''
        node-gyp --tarball ${nodejsHeaders} rebuild
      '';
    };
  };

  buildInputs = [ cacert webCommon ];

  nativeBuildInputs = [ git easyPS.purs easyPS.spago easyPS.psc-package nodePackages_10_x.node-gyp nodejs-10_x python2 ];

  buildPhase = ''
    export HOME=$NIX_BUILD_TOP
    export SASS_BINARY_PATH=${if stdenv.isDarwin then nodeSassBinDarwin else nodeSassBinLinux}

    # mkYarnPackage moves everything into deps/${name}
    shopt -s extglob
    mkdir deps
    mv !(deps) deps/
    cd deps

    # move everything into its correct place
    cp -R ${psSrc} generated
    cp -R ${webCommon} ../web-common
    sh ${spagoPackages.installSpagoStyle}

    # Compile everything.
    # This should just be `spago --no-psa build`, but there's a bug in spago that means it would go to the internet.
    # When that changes, update.
    purs compile \
      'src/**/*.purs' \
      'test/**/*.purs' \
      'generated/**/*.purs' \
      '../web-common/**/*.purs' \
      '.spago/*/*/src/**/*.purs'

    # Build the frontend.
    yarn --offline webpack
  '';

  doCheck = true;

  checkPhase = ''
    node -e 'require("./output/Test.Main").main()'
  '';

  distPhase = ''
    true
  '';

  installPhase = ''
    mv dist $out
  '';
}
