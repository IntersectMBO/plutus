{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "1.18";
      identifier = { name = "plutus-tx"; version = "0.1.0.0"; };
      license = "BSD-3-Clause";
      copyright = "Copyright: (c) 2018 Input Output";
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
          (hsPkgs.plutus-tx-plugin)
          ];
        };
      tests = {
        "plutus-tx-tests" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.language-plutus-core)
            (hsPkgs.plutus-tx-plugin)
            (hsPkgs.plutus-tx)
            (hsPkgs.plutus-ir)
            (hsPkgs.prettyprinter)
            (hsPkgs.mtl)
            (hsPkgs.template-haskell)
            (hsPkgs.tasty)
            ];
          };
        "plutus-tx-tutorial-doctests" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.plutus-tx)
            (hsPkgs.plutus-tx-plugin)
            (hsPkgs.language-plutus-core)
            (hsPkgs.prettyprinter)
            (hsPkgs.doctest)
            ];
          build-tools = [ ((hsPkgs.buildPackages).markdown-unlit) ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../plutus-tx; }