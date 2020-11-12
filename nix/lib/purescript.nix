{ stdenv
, pkgs
, fetchurl
, psSrc
, easyPS
, yarn2nix-moretea
, nodejs-headers
, src
, additionalPurescriptSources ? [ ]
, packages
, spagoPackages
, name
, packageJSON
, yarnLock
, yarnNix
, webCommon
, checkPhase ? "yarn --offline test"
, passthru ? { }
}:

with pkgs;

let

  # node-sass is terrible and we have to get it its binaries otherwise it will try to build them
  nodeSassBinLinux = fetchurl {
    url = "https://github.com/sass/node-sass/releases/download/v4.11.0/linux-x64-64_binding.node";
    sha256 = "0dl91l414na44h090cgghd06q0j2whlj9h98im2qb9823glq7xff";
  };
  nodeSassBinDarwin = fetchurl {
    url = "https://github.com/sass/node-sass/releases/download/v4.11.0/darwin-x64-64_binding.node";
    sha256 = "1p5gz1694vxar81hbrrbdmmr2wjw3ksfvfgwh0kzzgjkc2dpk5pa";
  };

  packagesJson = "${src}/packages.json";

  cleanSrcs = pkgs.lib.cleanSourceWith {
    filter = pkgs.lib.cleanSourceFilter;
    src = lib.cleanSourceWith {
      filter = (path: type: !(pkgs.lib.elem (baseNameOf path)
        [ ".spago" ".spago2nix" "generated" "generated-docs" "output" "dist" "node_modules" ".psci_modules" ".vscode" ]));
      inherit src;
    };
  };

  purescriptSources = [
    "src/**/*.purs"
    "test/**/*.purs"
    "generated/**/*.purs"
    ".spago/*/*/src/**/*.purs"
  ] ++ additionalPurescriptSources;

in
yarn2nix-moretea.mkYarnPackage {
  inherit name packageJSON yarnLock yarnNix checkPhase passthru;
  src = cleanSrcs;
  nodejs = nodejs-10_x;

  pkgConfig = {
    "libxmljs" = {
      buildInputs = [ nodejs-10_x python2 ];
      postInstall = ''
        # To deal with some OSX setups we need to use the version of node-gyp that's patched in
        # https://github.com/NixOS/nixpkgs/blob/master/pkgs/development/web/nodejs/nodejs.nix#L106
        ${nodejs-10_x}/lib/node_modules/npm/bin/node-gyp-bin/node-gyp --tarball ${nodejs-headers} rebuild
      '';
    };
  };

  buildInputs = [ cacert ];

  nativeBuildInputs = [ git easyPS.purs easyPS.spago easyPS.psc-package nodePackages_10_x.node-gyp nodejs-10_x python2 ];

  buildPhase = ''
    export HOME=$NIX_BUILD_TOP
    export SASS_BINARY_PATH=${if stdenv.isDarwin then nodeSassBinDarwin else nodeSassBinLinux}

    # Ensure that the shell expands 'foo/**/*.purs' to include 'foo/*.purs'.
    shopt -s globstar

    # Recent versions of yarn2nix moved the package source
    # into deps/${name} with a .yarnrc that magically uses
    # that as the PWD. This doesn't work for us since we're
    # not just using yarn, so we undo that.
    # (The node_mdules is just a symlink to something empty,
    # the real one seems to be in the root, I don't understand
    # why. We remove it so we can copy without conflicts.)
    rm deps/${name}/node_modules
    cp -R deps/${name}/* .
    rm .yarnrc

    # Put links to the generated and common source in the correct place.
    ln -s ${psSrc} generated
    ln -s ${webCommon} ../web-common

    # Ask spago to make the PureScript packages available.
    sh ${spagoPackages.installSpagoStyle}

    # Compile everything.
    purs compile ${builtins.concatStringsSep " " purescriptSources}

    # Build the frontend.
    yarn --offline webpack
  '';

  doCheck = true;

  distPhase = ''
    true
  '';

  installPhase = ''
    mv dist $out
  '';

  # A bunch of this stuff doesn't seem to work on darwin
  meta.platforms = pkgs.lib.platforms.linux;
}
