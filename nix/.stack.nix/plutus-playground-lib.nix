{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "1.10";
      identifier = { name = "plutus-playground-lib"; version = "0.1.0.0"; };
      license = "BSD-3-Clause";
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
          (hsPkgs.base64-bytestring)
          (hsPkgs.bytestring)
          (hsPkgs.containers)
          (hsPkgs.plutus-tx)
          (hsPkgs.plutus-tx-plugin)
          (hsPkgs.http-media)
          (hsPkgs.insert-ordered-containers)
          (hsPkgs.memory)
          (hsPkgs.mtl)
          (hsPkgs.transformers)
          (hsPkgs.lens)
          (hsPkgs.network)
          (hsPkgs.newtype-generics)
          (hsPkgs.plutus-use-cases)
          (hsPkgs.servant)
          (hsPkgs.split)
          (hsPkgs.swagger2)
          (hsPkgs.template-haskell)
          (hsPkgs.text)
          (hsPkgs.wallet-api)
          ];
        };
      tests = {
        "playground-lib-test" = {
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
    } // rec {
    src = (pkgs.lib).mkDefault .././../plutus-playground/plutus-playground-lib;
    }