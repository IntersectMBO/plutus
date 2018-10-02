{ supportedSystems ? [ "x86_64-linux" "x86_64-darwin" ]
, scrubJobs ? true
, nixpkgs
}:

let
  packageSet = args: import ./. ({ inherit nixpkgs; } // args);
  releaseLib = (import (nixpkgs + "/pkgs/top-level/release-lib.nix") {
    inherit supportedSystems scrubJobs packageSet;
  });
  pkgs = import nixpkgs { config = {}; };

  plutusPkgs = packageSet;

  platformBuilds = releaseLib.mapTestOn {
    plutus-prototype = supportedSystems;
    language-plutus-core = supportedSystems;
    plutus-core-interpreter = supportedSystems;
    plutus-exe = supportedSystems;
    core-to-plc = supportedSystems;
    plutus-th = supportedSystems;
    plutus-use-cases = supportedSystems;
    wallet-api = supportedSystems;
    # don't need to build the spec on anything other than one platform
    plutus-core-spec = [ "x86_64-linux" ];
  };

  testBuilds = {
    inherit (plutusPkgs {}) tests;
  };
in platformBuilds // testBuilds
