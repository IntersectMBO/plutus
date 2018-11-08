let
  fixedLib     = import ./lib.nix;
  fixedNixpkgs = fixedLib.fetchNixpkgs;
in
  { supportedSystems ? [ "x86_64-linux" "x86_64-darwin" ]
  , scrubJobs ? true
  , fasterBuild ? false
  , skipPackages ? []
  , nixpkgsArgs ? {
      config = { allowUnfree = false; inHydra = true; };
      inherit fasterBuild;
    }
  }:

with (import (fixedNixpkgs + "/pkgs/top-level/release-lib.nix") {
  inherit supportedSystems scrubJobs nixpkgsArgs;
  packageSet = import ./.;
});

let
  plutusPkgs = import ./. { };
  pkgs = import fixedNixpkgs { config = {}; };
  shellEnv = import ./shell.nix { };
  platforms = {
    haskellPackages = {
      language-plutus-core = supportedSystems;
      plutus-core-interpreter = supportedSystems;
      plutus-exe = supportedSystems;
      core-to-plc = supportedSystems;
      plutus-ir = supportedSystems;
      plutus-th = supportedSystems;
      plutus-use-cases = supportedSystems;
      wallet-api = supportedSystems;
    };
    # don't need to build the spec on anything other than one platform
    plutus-core-spec = [ "x86_64-linux" ];
  };
  mapped = mapTestOn platforms;
  makePlutusTestRuns = system:
  let
    pred = name: value: fixedLib.isPlutus name && value ? testrun;
    plutusPkgs = import ./. { inherit system; };
    f = name: value: value.testrun;
  in pkgs.lib.mapAttrs f (lib.filterAttrs pred plutusPkgs.haskellPackages);
in pkgs.lib.fix (jobsets:  mapped // {
  inherit (plutusPkgs) tests;
  all-plutus-tests.x86_64-linux = makePlutusTestRuns "x86_64-linux";
  required = pkgs.lib.hydraJob (pkgs.releaseTools.aggregate {
    name = "plutus-required-checks";
    constituents =
      let
        allLinux = x: map (system: x.${system}) [ "x86_64-linux" ];
      in
    [
      (builtins.concatLists (map lib.attrValues (allLinux jobsets.all-plutus-tests)))
      jobsets.tests.hlint
      jobsets.tests.shellcheck
      jobsets.tests.stylishHaskell
    ];
  });
})
