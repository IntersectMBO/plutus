{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "2.2";
      identifier = { name = "plutus-tx"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones";
      homepage = "";
      url = "";
      synopsis = "The PlutusTx compiler frontend";
      description = "The PlutusTx compiler frontend";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.bytestring)
          (hsPkgs.template-haskell)
          (hsPkgs.language-plutus-core)
          (hsPkgs.plutus-core-interpreter)
          (hsPkgs.plutus-tx-compiler)
          ];
        build-tools = [ ((hsPkgs.buildPackages).doctest) ];
        };
      sublibs = {
        "plutus-tx-compiler" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.bytestring)
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
        };
      tests = {
        "plutus-tx-tests" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.language-plutus-core)
            (hsPkgs.plutus-tx)
            (hsPkgs.plutus-ir)
            (hsPkgs.prettyprinter)
            (hsPkgs.mtl)
            (hsPkgs.bytestring)
            (hsPkgs.template-haskell)
            (hsPkgs.tasty)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././plutus-tx; }