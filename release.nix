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
    language-plutus-core = supportedSystems;
    plutus-core-interpreter = supportedSystems;
    plutus-exe = supportedSystems;
    core-to-plc = supportedSystems;
    plutus-ir = supportedSystems;
    plutus-th = supportedSystems;
    plutus-use-cases = supportedSystems;
    wallet-api = supportedSystems;
    # don't need to build the spec on anything other than one platform
    plutus-core-spec = [ "x86_64-linux" ];
  };
  mapped = mapTestOn platforms;
in mapped // {
  tests = plutusPkgs.tests;
}
