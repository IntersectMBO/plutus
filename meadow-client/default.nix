{ stdenv, pkgs, fetchurl, psSrc }:

with pkgs;

let
  yarnDeps = import ./yarn.nix { inherit fetchurl linkFarm; };
  patchShebangs = dir: ''
    node=`type -p node`
    coffee=`type -p coffee || true`
    find -L ${dir} -type f -print0 | xargs -0 grep -Il . | \
    xargs sed --follow-symlinks -i \
        -e 's@#!/usr/bin/env node@#!'"$node"'@' \
        -e 's@#!/usr/bin/env coffee@#!'"$coffee"'@' \
        -e 's@#!/.*/node@#!'"$node"'@' \
        -e 's@#!/.*/coffee@#!'"$coffee"'@' || true
  '';

  # node-sass is terrible and we have to get it its binaries otherwise it will try to build them
  nodeSassBinLinux = fetchurl {
    url = "https://github.com/sass/node-sass/releases/download/v4.11.0/linux-x64-48_binding.node";
    sha256 = "0by4hp7wxdzl8dq5svs2c11i93zsdkmn1v2009lqcrw3jyg6fxym";
  };
  nodeSassBinDarwin = fetchurl {
    url = "https://github.com/sass/node-sass/releases/download/v4.11.0/darwin-x64-48_binding.node";
    sha256 = "11jik9r379dxnx5v9h79sirqlk7ixdspnccfibzd4pgm6s2mw4vn";
  };
  webCommon = pkgs.copyPathToStore ../web-common;
in stdenv.mkDerivation {
  srcs = ./.;

  name = "meadow-client";

  buildInputs = [ nodejs yarn git cacert purescript yarnDeps.offline_cache python2 webCommon ];

  bowerComponents = pkgs.buildBowerComponents {
    name = "my-web-app";
    generated = ./bower-packages.nix;
    src = ./.;
  };

  configurePhase = ''
    export HOME="$NIX_BUILD_TOP"
    export SASS_BINARY_PATH=${if stdenv.isDarwin then nodeSassBinDarwin else nodeSassBinLinux}

    sed -i -E 's|^(\s*resolved\s*")https?://.*/|\1|' yarn.lock
    yarn --offline config set yarn-offline-mirror ${yarnDeps.offline_cache}
    yarn --offline config set yarn-offline-mirror-pruning true
    yarn --offline install

    ${patchShebangs "node_modules/.bin/"}

    mkdir generated
    mkdir ../web-common
    cp -R ${psSrc}/* generated/
    cp -R ${webCommon}/* ../web-common/
    cp --reflink=auto --no-preserve=mode -R $bowerComponents/bower_components .
  '';

  buildPhase = ''
    yarn --offline run webpack
  '';

  doCheck = true;

  checkPhase = ''
    yarn test
  '';

  installPhase = ''
    mv dist $out
  '';
}
