{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "2.0";
      identifier = { name = "plutus-playground-lib"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "2018 IOHK";
      maintainer = "kris.jenkins@tweag.io";
      author = "Kris Jenkins";
      homepage = "https://github.com/iohk/plutus#readme";
      url = "";
      synopsis = "";
      description = "Please see the README on GitHub at <https://github.com/input-output-hk/plutus#readme>";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.aeson)
          (hsPkgs.base)
          (hsPkgs.bytestring)
          (hsPkgs.containers)
          (hsPkgs.insert-ordered-containers)
          (hsPkgs.interpreter)
          (hsPkgs.lens)
          (hsPkgs.memory)
          (hsPkgs.mtl)
          (hsPkgs.newtype-generics)
          (hsPkgs.servant)
          (hsPkgs.swagger2)
          (hsPkgs.template-haskell)
          (hsPkgs.text)
          (hsPkgs.transformers)
          (hsPkgs.wallet-api)
          ];
        };
      tests = {
        "plutus-playground-lib-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.containers)
            (hsPkgs.hedgehog)
            (hsPkgs.swagger2)
            (hsPkgs.tasty)
            (hsPkgs.tasty-hunit)
            (hsPkgs.text)
            (hsPkgs.template-haskell)
            (hsPkgs.plutus-playground-lib)
            (hsPkgs.wallet-api)
            (hsPkgs.aeson)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../plutus-playground-lib; }