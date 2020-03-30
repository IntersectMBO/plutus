let
  localLib     = import ./lib.nix;
  fixedNixpkgs = (import ./nix/sources.nix { }).nixpkgs;
  nixpkgs = import fixedNixpkgs { };
  lib = nixpkgs.lib;
  linux = ["x86_64-linux"];
  darwin = ["x86_64-darwin"];
in
  { supportedSystems ? linux ++ darwin
  , scrubJobs ? true
  , nixpkgsArgs ? {
      # we need unfree for kindlegen
      config = { allowUnfree = false;
                 allowUnfreePredicate = localLib.unfreePredicate;
                 inHydra = true;
                 };
    }
  # Passed in by Hydra depending on the configuration, contains the revision and the out path
  , plutus ? null
  }:

# The revision passed in by Hydra, if there is one
let rev = if builtins.isNull plutus then null else plutus.rev;
    ci = import ./ci.nix;

in with (import (fixedNixpkgs + "/pkgs/top-level/release-lib.nix") {
  inherit supportedSystems scrubJobs;
  nixpkgsArgs = nixpkgsArgs // { inherit rev; };
  packageSet = import ./.;
});

let
  packageSet = import ./. { inherit rev; checkMaterialization = true; };
  # Makes a tree of attributes where some nodes are replaced with just the
  # list of systems which we want to the hydra jobs to run on.
  mapDerivationsToSystemsRecursive = sys:
    lib.mapAttrsRecursiveCond
      # Only recurse into attributes marked with `recurseForDerivations`.
      # This avoids us looking to deeply (or even recusing infinitely)
      # This mark is usually added with `pkgs.recurseIntoAttrs`
      # https://github.com/NixOS/nixpkgs/blob/fd98b29b293f868636fa2f6cf54d7df334bdd3d9/pkgs/top-level/all-packages.nix#L65-L67
      (x: x.recurseForDerivations or false)
      # Replace each node in the tree with the provided list of systems
      # or an empty list if the node is not a derivation.
      (_: x: lib.optionals (lib.isDerivation x) sys);
  # Hydra doesn't like these attributes hanging around in "jobsets": it thinks they're jobs!
  stripCiAttrs = lib.filterAttrsRecursive (n: _: n != "recurseForDerivations" && n != "dimension");

  # This is a mapping from attribute paths to systems. So it needs to mirror the structure of the
  # attributes in default.nix exactly
  systemMapping = {
    # At least the client is broken on darwin for some yarn reason
    plutus-playground = lib.mapAttrs (_: _: linux) packageSet.plutus-playground;
    # At least the client is broken on darwin for some yarn reason
    marlowe-playground = lib.mapAttrs (_: _: linux) packageSet.marlowe-playground;
    # texlive is broken on darwin at our nixpkgs pin
    docs = lib.mapAttrs (_: _: linux) packageSet.docs;
    papers = lib.mapAttrs (_: _: linux) packageSet.papers;
    tests = lib.mapAttrs (_: _: supportedSystems) packageSet.tests;
    dev.haskellNixRoots = mapDerivationsToSystemsRecursive supportedSystems packageSet.dev.haskellNixRoots;
    # See note on 'easyPS' in 'default.nix'
    dev.scripts = lib.mapAttrs (n: _: if n == "updateClientDeps" then linux else supportedSystems) packageSet.dev.scripts;
  };

  testJobsets =
    mapTestOn systemMapping
    # ci.nix is a set of attributes that work fine as jobs (albeit in a slightly different structure, the platform comes
    # first), but we mainly just need to get rid of the 'recurseForDerivation' attributes.
    // (stripCiAttrs ci);

  # Recursively collect all jobs (derivations) in a jobset
  allJobs = jobset: lib.collect lib.isDerivation jobset;

in lib.fix (jobsets: testJobsets // {
  required = lib.hydraJob (nixpkgs.releaseTools.aggregate {
    name = "plutus-required-checks";

    constituents =
      (allJobs jobsets.tests)
      ++ (allJobs jobsets.docs)
      ++ (allJobs jobsets.papers)
      ++ (allJobs jobsets.plutus-playground)
      ++ (allJobs jobsets.marlowe-playground)
      ++ (allJobs jobsets.dev.scripts);
  });
})
