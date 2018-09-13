let
  fixedNixpkgs = (import ./lib.nix).fetchNixPkgs;
in
  { supportedSystems ? [ "x86_64-linux" "x86_64-darwin" ]
  , scrubJobs ? true
  }:

with (import (fixedNixpkgs + "/pkgs/top-level/release-lib.nix") {
  inherit supportedSystems scrubJobs;
  packageSet = import ./.;
});

let
  plutusPkgs = import ./. { };
  pkgs = import fixedNixpkgs { config = {}; };
  platforms = {
    plutus-prototype = supportedSystems;
    language-plutus-core = supportedSystems;
    plutus-core-interpreter = supportedSystems;
    plutus-core-spec = supportedSystems;
  };
  mapped = mapTestOn platforms;
in mapped // {
  tests = plutusPkgs.tests;
}
