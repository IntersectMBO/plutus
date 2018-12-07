{ stdenv, pkgs, psSrc }:

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

in {
  plutus-playground-client = stdenv.mkDerivation {
    src = ./.;

    name = "plutus-playground-client";

    buildInputs = [ nodejs yarn git cacert purescript yarnDeps.offline_cache python2 ];

    bowerComponents = pkgs.buildBowerComponents {
      name = "my-web-app";
      generated = ./bower-packages.nix;
      src = ./.;
    };

    configurePhase = ''
      export HOME="$NIX_BUILD_TOP"

      sed -i -E 's|^(\s*resolved\s*")https?://.*/|\1|' yarn.lock
      yarn --offline config set yarn-offline-mirror ${yarnDeps.offline_cache}
      yarn --offline config set yarn-offline-mirror-pruning true
      yarn --offline install

      ${patchShebangs "node_modules/.bin/"}

      cp -R ${psSrc}/* ./src/
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
  };
}
