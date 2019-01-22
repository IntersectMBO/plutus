{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "1.18";
      identifier = { name = "core-to-plc"; version = "0.1.0.0"; };
      license = "BSD-3-Clause";
      copyright = "Copyright: (c) 2018 Input Output";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones";
      homepage = "";
      url = "";
      synopsis = "GHC Core to Plutus Core compiler";
      description = "Complier that converts GHC Core to Plutus Core";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.bytestring)
          (hsPkgs.cborg)
          (hsPkgs.containers)
          (hsPkgs.ghc)
          (hsPkgs.language-plutus-core)
          (hsPkgs.mmorph)
          (hsPkgs.microlens)
          (hsPkgs.mtl)
          (hsPkgs.prettyprinter)
          (hsPkgs.serialise)
          (hsPkgs.template-haskell)
          (hsPkgs.text)
          (hsPkgs.transformers)
          ];
        };
      tests = {
        "core-to-plc-plugin" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.core-to-plc)
            (hsPkgs.language-plutus-core)
            (hsPkgs.bytestring)
            (hsPkgs.mtl)
            (hsPkgs.text)
            (hsPkgs.prettyprinter)
            (hsPkgs.tasty)
            (hsPkgs.tasty-hunit)
            (hsPkgs.tasty-golden)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../core-to-plc; }