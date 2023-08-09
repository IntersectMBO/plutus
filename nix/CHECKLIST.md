{ inputs, cell }:

self: super: {

  # TODO: not sure if this patch is still needed
  rPackages = super.rPackages.override {
    overrides = ({
      hexbin = super.rPackages.hexbin.overrideDerivation (attrs: {
        nativeBuildInputs = attrs.nativeBuildInputs ++ [ super.libiconv ];
        buildInputs = attrs.buildInputs ++ [ super.libiconv ];
      });
    });
  };

}


      # Build all the haddock for all the components that have it. This ensures that it all
      # builds properly on all the GHC versions we're testing.
      haddock =
        let
          allComponents = lib.collect (x: lib.isDerivation x) components;
          allHaddocks = pkgs.lib.concatMap (x: lib.optional (x ? doc) x.doc) allComponents;
        in
        pkgs.releaseTools.aggregate {
          name = "all-haddock";
          meta.description = "All haddock for all components";
          constituents = allHaddocks;
        };