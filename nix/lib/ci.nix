let
  # Generic nixpkgs, use *only* for lib functions that are stable across versions
  pkgs = import (import ../sources.nix).nixpkgs { };
  lib = pkgs.lib;
in
rec {
  # Borrowed from https://github.com/cachix/ghcide-nix/pull/4/files#diff-70bfff902f4dec33e545cac10ee5844d
  # Tweaked to use builtins.mapAttrs instead of needing the one from nixpkgs lib
  /*
    dimension: name -> attrs -> function -> attrs
    where
      function: keyText -> value -> attrsOf package

    WARNING: Attribute names must not contain periods (".").
             See https://github.com/NixOS/nix/issues/3088

    NOTE: The dimension name will be picked up by agent and web ui soon.

    Specifies a dimension of the build matrix. For example

        dimension "Example" {
          withP = { p = true; }
          withoutP = { p = false; }
        } (key:      # either "withP" or "withoutP"
          { p }:     # either p = true or p = false
          myProject p
        )

    evaluates roughly to

        {
          withP = myProject true;
          withoutP = myProject false;
        }

    Use nested calls for multiple dimensions.

    Example:

        dimension "System" {
          "x86_64-linux" = {};
          # ...
          }: (system: {}:

          dimension "Nixpkgs release" (
            {
              "nixpkgs-19_03".nixpkgs = someSource
            } // optionalAttrs (system != "...") {
              "nixpkgs-unstable".nixpkgs = someOtherSource
            }
            ) (_key: { nixpkgs }:

            myProject system nixpkgs

          )
        )

    evaluates roughly to

        {
          x86_64-linux.nixpkgs-19_03 = myProject "x86_64-linux" someSource;
          x86_64-linux.nixpkgs-unstable = myProject "x86_64-linux" someOtherSource;
          ...
        }

    If you need to make references across attributes, you can do so by binding
    the result. Wherever you write

        dimension "My dimension" {} (key: value: f1 key value)

    You can also write

        let
          myDimension = dimension "My dimension" {} (key: value: f2 key value myDimension)
        in
          myDimension

    This example builds a single test runner to reuse across releases:

        let
          overlay =
            testRunnerPkgs: self: super: {
              # ...
            };
          myProject =
            { nixpkgs,
              pkgs ? import nixpkgs { overlays = [ overlay ]; },
              testRunnerPkgs ? pkgs
            }: pkgs;
        in

        let
          latest = "nixpkgs-19_03";
          releases =
            dimension "Nixpkgs release"
              {
                nixpkgs-18_09.nixpkgs = someSource
                nixpkgs-19_03.nixpkgs = someOtherSource
              }
              (_key: { nixpkgs }:

                myProject {
                  inherit nixpkgs;
                  testRunnerPkgs = releases."${latest}";
                }

              );
        in releases;

   */
  dimension = name: attrs: f:
    builtins.mapAttrs
      (k: v:
        let o = f k v;
        in o // { recurseForDerivations = o.recurseForDerivations or true; }
      )
      attrs
    // { meta.dimension.name = name; };

  # A filter for removing packages that aren't supported on the current platform
  # according to 'meta.platforms'.
  platformFilterGeneric = pkgs: system:
    # This needs to use the correct nixpkgs version so all the systems line up
    let
      lib = pkgs.lib;
      platform = lib.systems.elaborate { inherit system; };
      # Can't just default to [] for platforms, since no meta.platforms
      # means "all platforms" not "no platforms"
    in
    drv:
    if drv ? meta && drv.meta ? platforms then
      lib.any (lib.meta.platformMatch platform) drv.meta.platforms
    else true;

  # Hydra doesn't like these attributes hanging around in "jobsets": it thinks they're jobs!
  stripAttrsForHydra = filterAttrsOnlyRecursive (n: _: n != "recurseForDerivations" && n != "dimension");

  # Keep derivations and attrsets with 'recurseForDerivations'. This ensures that we match the
  # derivations that Hercules will see, and prevents Hydra from trying to pick up all sorts of bad stuff
  # (like attrsets that contain themselves!).
  filterDerivations = filterAttrsOnlyRecursive (n: attrs: lib.isDerivation attrs || attrs.recurseForDerivations or false);

  # A version of 'filterAttrsRecursive' that doesn't recurse into derivations. This prevents us from going into an infinite
  # loop with the 'out' attribute on derivations.
  # TODO: Surely this shouldn't be necessary. I think normal 'filterAttrsRecursive' will effectively cause infinite loops
  # if you keep derivations and your predicate forces the value of the attribute, as this then triggers a loop on the
  # 'out' attribute. Weird.
  filterAttrsOnlyRecursive = pred: set:
    lib.listToAttrs (
      lib.concatMap
        (name:
          let v = set.${name}; in
          if pred name v then [
            (lib.nameValuePair name (
              if builtins.isAttrs v && !lib.isDerivation v then filterAttrsOnlyRecursive pred v
              else v
            ))
          ] else [ ]
        )
        (builtins.attrNames set)
    );
}
