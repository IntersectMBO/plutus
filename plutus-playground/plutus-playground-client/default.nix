{ stdenv, pkgs }:

with pkgs;

let
  yarnDeps = import ./yarn.nix { inherit fetchurl linkFarm; };
  offlineCache = yarnDeps.offline_cache;
in {
  plutus-playground-client = stdenv.mkDerivation {
    src = ./.;
  
    name = "plutus-playground-client";
  
    buildInputs = [ nodejs yarn git cacert purescript ];
  
    configurePhase = ''
      export HOME="$NIX_BUILD_TOP"
  
      # yarn config --offline set yarn-offline-mirror ${offlineCache}
  
      # yarn install --offline --frozen-lockfile --ignore-engines --ignore-scripts
    '';
  
    buildPhase = ''
      yarn
      yarn run bower install
      yarn run webpack
      ls
    '';
  
    doCheck = false;
  
    checkPhase = ''
      yarn test --coverage --ci --no-color
    '';
  
    installPhase = ''
      mv dist $out
    '';
  };
}
