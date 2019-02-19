{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "2.0";
      identifier = { name = "plutus-use-cases"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "jann.mueller@iohk.io";
      author = "Manuel M T Chakravarty, Jann Müller";
      homepage = "";
      url = "";
      synopsis = "Collection of smart contracts to develop the plutus/wallet interface";
      description = "Collection of smart contracts to develop the plutus/wallet interface.";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.bytestring)
          (hsPkgs.containers)
          (hsPkgs.mtl)
          (hsPkgs.template-haskell)
          (hsPkgs.plutus-tx)
          (hsPkgs.wallet-api)
          (hsPkgs.lens)
          ];
        };
      tests = {
        "plutus-use-cases-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.containers)
            (hsPkgs.hedgehog)
            (hsPkgs.tasty)
            (hsPkgs.tasty-hunit)
            (hsPkgs.tasty-hedgehog)
            (hsPkgs.text)
            (hsPkgs.wallet-api)
            (hsPkgs.plutus-use-cases)
            (hsPkgs.plutus-tx)
            (hsPkgs.template-haskell)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../plutus-use-cases; }