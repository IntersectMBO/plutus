let
  localLib     = import ./lib.nix { };
  fixedNixpkgs = localLib.nixpkgs;
  nixpkgs = import fixedNixpkgs { };
  lib = nixpkgs.lib;
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
  packageSet = import ./. { };

  # This is a mapping from attribute paths to systems. So it needs to mirror the structure of the
  # attributes in default.nix exactly
  systemMapping = supportedSystems: {
    localPackages = 
      # Due to the magical split test machinery, packages that have a 'testdata' attribute should
      # have their tests run via the 'testrun' derivation. I don't know how to *also* have a mapping
      # for the package itself, since it would collide with the attrset containing 'testrun', but 
      # the tests will depend on the main package so that's okay.
      lib.mapAttrs (n: p: if p ? testdata then { testrun = supportedSystems; } else supportedSystems)
         packageSet.localPackages;
    plutus-playground = lib.mapAttrs (_: _: supportedSystems) 
        (lib.filterAttrs (n: v: n != "docker") packageSet.plutus-playground);  
    meadow = lib.mapAttrs (_: _: supportedSystems) 
        (lib.filterAttrs (n: v: n != "docker") packageSet.meadow);  
    docs = lib.mapAttrs (_: _: supportedSystems) packageSet.docs;  
    tests = lib.mapAttrs (_: _: supportedSystems) packageSet.tests;  
    dev.packages = lib.mapAttrs (_: _: supportedSystems) packageSet.dev.packages;  
    dev.scripts = lib.mapAttrs (_: _: supportedSystems) packageSet.dev.scripts;  
  }; 
  
  testJobsets = mapTestOn (systemMapping supportedSystems);

  # Recursively collect all jobs (derivations) in a jobset 
  allJobs = jobset: lib.collect lib.isDerivation jobset;

in lib.fix (jobsets: testJobsets // {
  required = lib.hydraJob (nixpkgs.releaseTools.aggregate {
    name = "plutus-required-checks";
    
    constituents = (allJobs jobsets.localPackages)
      ++ (allJobs jobsets.tests)
      ++ (allJobs jobsets.docs) 
      ++ (allJobs jobsets.plutus-playground)
      ++ (allJobs jobsets.meadow)
      ++ (allJobs jobsets.dev.scripts);
  });
})
