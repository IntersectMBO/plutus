{ stdenv
, lib
, linkFarm
, cacert
, nodejs
, nodePackages
, python2
, git
, fetchurl
, yarn2nix-moretea
, nodejs-headers
, easyPS
}:

{ psSrc
, src
, name
, yarnLock ? src + "/yarn.lock"
, yarnNix ? src + "/yarn.nix"
, packageJSON ? src + "/package.json"
, additionalPurescriptSources ? [ ]
, packages
, spagoPackages
, webCommon
, checkPhase ? "yarn --offline test"
, passthru ? { }
}:

let

  # Note that these binaries are both versioned with the node-sass version *and* the NODE_MODULE_VERSION
  # version, so you may need to change that when updating to a new version of nodejs.
  # For reasons beyond my ken, these do *not* work if you try and get them with niv. Mysteriously you get snytax
  # errors in the binding, even though diffing the files they look the same. I gave up and left them like ths.
  nodeSassBinLinux = fetchurl {
    url = "https://github.com/sass/node-sass/releases/download/v5.0.0/linux-x64-72_binding.node";
    sha256 = "0ja9b462dzxmkqm15zc0flv33cq16jy86vigj7gbmmad2pgkryq8";
  };
  nodeSassBinDarwin = fetchurl {
    url = "https://github.com/sass/node-sass/releases/download/v5.0.0/darwin-x64-72_binding.node";
    sha256 = "0b079cygjr3i70hwvb1ik83z2lxbbl1daqky0i8mnbibxbgr4jb7";
  };
  nodeSassBinDir = linkFarm "node-sass-bin-dir" [
    { name = "linux-x64-72/binding.node"; path = nodeSassBinLinux; }
    { name = "darwin-x64-72/binding.node"; path = nodeSassBinDarwin; }
  ];

  packagesJson = "${src}/packages.json";

  cleanSrcs = lib.cleanSourceWith {
    filter = lib.cleanSourceFilter;
    src = lib.cleanSourceWith {
      filter = (path: type: !(lib.elem (baseNameOf path)
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
  inherit name packageJSON yarnLock yarnNix checkPhase passthru nodejs;
  src = cleanSrcs;

  pkgConfig = {
    "libxmljs" = {
      buildInputs = [ nodejs python2 ];
      postInstall = ''
        # To deal with some OSX setups we need to use the version of node-gyp that's patched in
        # https://github.com/NixOS/nixpkgs/blob/master/pkgs/development/web/nodejs/nodejs.nix#L106
        ${nodejs}/lib/node_modules/npm/bin/node-gyp-bin/node-gyp --tarball ${nodejs-headers} rebuild
      '';
    };
  };

  buildInputs = [ cacert ];

  nativeBuildInputs = [ git easyPS.purs easyPS.spago easyPS.psc-package nodePackages.node-gyp nodejs python2 ];

  buildPhase = ''
    export HOME=$NIX_BUILD_TOP
    # node-sass is terrible and we need to fix the binaries otherwise it will try and download them
    export SASS_BINARY_DIR=${nodeSassBinDir}

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
  meta.platforms = lib.platforms.linux;
}
