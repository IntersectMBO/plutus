let
  fixedLib     = import ./lib.nix { };
  fixedNixpkgs = fixedLib.nixpkgs;
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
  pkgs = import fixedNixpkgs { };
  haskellPackages = map (name: lib.nameValuePair name supportedSystems) fixedLib.plutusPkgList;
  # don't need to build the docs on anything other than one platform
  docs = map (name: lib.nameValuePair name [ "x86_64-linux" ]) (builtins.attrNames plutusPkgs.docs);
  platforms = {
    inherit haskellPackages;
    inherit docs;
  };
  mapped = mapTestOn platforms;
  makePlutusTestRuns = system:
    let
      pred = name: value: fixedLib.isPlutus name;
      plutusPkgs = import ./. { inherit system; };
      # for things which are split-check then take the test run, otherwise
      # use the main derivation which will have the tests as part of it
      f = name: value: if value ? testdata then value.testrun else value;
    in pkgs.lib.mapAttrs f (lib.filterAttrs pred plutusPkgs.haskellPackages);
in pkgs.lib.fix (jobsets:  mapped // {
  inherit (plutusPkgs) tests docs plutus-playground-client;
  all-plutus-tests = builtins.listToAttrs (map (arch: { name = arch; value = makePlutusTestRuns arch; }) supportedSystems);
  required = pkgs.lib.hydraJob (pkgs.releaseTools.aggregate {
    name = "plutus-required-checks";
    constituents =
      let
        allLinux = x: map (system: x.${system}) [ "x86_64-linux" ];
        all = x: map (system: x.${system}) supportedSystems;
      in
    [
      (builtins.concatLists (map lib.attrValues (all jobsets.all-plutus-tests)))
    ] ++ (builtins.attrValues jobsets.tests) ++ (builtins.attrValues jobsets.docs) ++ [jobsets.plutus-playground-client];
  });
})
