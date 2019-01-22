{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "1.18";
      identifier = { name = "plutus-tx-plugin"; version = "0.1.0.0"; };
      license = "BSD-3-Clause";
      copyright = "Copyright: (c) 2018 Input Output";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones";
      homepage = "";
      url = "";
      synopsis = "PlutusTx compiler plugin";
      description = "GHC compiler plugin for the PlutusTx compiler";
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
          (hsPkgs.lens)
          (hsPkgs.mtl)
          (hsPkgs.plutus-ir)
          (hsPkgs.prettyprinter)
          (hsPkgs.serialise)
          (hsPkgs.template-haskell)
          (hsPkgs.th-abstraction)
          (hsPkgs.text)
          (hsPkgs.transformers)
          ];
        };
      tests = {
        "plutus-tx-plugin-tests" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.plutus-tx-plugin)
            (hsPkgs.plutus-ir)
            (hsPkgs.prettyprinter)
            (hsPkgs.language-plutus-core)
            (hsPkgs.bytestring)
            (hsPkgs.tasty)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../plutus-tx-plugin; }