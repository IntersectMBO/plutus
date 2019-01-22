{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "1.18";
      identifier = { name = "plutus-th"; version = "0.1.0.0"; };
      license = "BSD-3-Clause";
      copyright = "Copyright: (c) 2018 Input Output";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones";
      homepage = "";
      url = "";
      synopsis = "TH frontend to the Plutus compiler";
      description = "TH frontend to the plutus compiler";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.template-haskell)
          (hsPkgs.core-to-plc)
          ];
        };
      tests = {
        "plutus-th-frontend" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.language-plutus-core)
            (hsPkgs.core-to-plc)
            (hsPkgs.plutus-th)
            (hsPkgs.template-haskell)
            (hsPkgs.bytestring)
            (hsPkgs.text)
            (hsPkgs.tasty)
            (hsPkgs.tasty-hunit)
            (hsPkgs.tasty-golden)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../plutus-th; }