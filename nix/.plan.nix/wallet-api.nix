{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "2.2";
      identifier = { name = "wallet-api"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones, Jann Mueller";
      homepage = "";
      url = "";
      synopsis = "Wallet API";
      description = "Wallet API and emulator";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.aeson)
          (hsPkgs.base16-bytestring)
          (hsPkgs.bytestring)
          (hsPkgs.cborg)
          (hsPkgs.containers)
          (hsPkgs.plutus-tx)
          (hsPkgs.cryptonite)
          (hsPkgs.hashable)
          (hsPkgs.hedgehog)
          (hsPkgs.language-plutus-core)
          (hsPkgs.memory)
          (hsPkgs.mtl)
          (hsPkgs.natural-transformation)
          (hsPkgs.operational)
          (hsPkgs.serialise)
          (hsPkgs.servant)
          (hsPkgs.servant-client)
          (hsPkgs.servant-server)
          (hsPkgs.stm)
          (hsPkgs.swagger2)
          (hsPkgs.template-haskell)
          (hsPkgs.text)
          (hsPkgs.transformers)
          (hsPkgs.recursion-schemes)
          (hsPkgs.lens)
          (hsPkgs.deriving-compat)
          (hsPkgs.newtype-generics)
          (hsPkgs.http-api-data)
          (hsPkgs.cardano-crypto)
          ];
        };
      exes = {
        "emulator" = {
          depends = [ (hsPkgs.base) (hsPkgs.wallet-api) (hsPkgs.warp) ];
          };
        };
      tests = {
        "wallet-api-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.containers)
            (hsPkgs.hedgehog)
            (hsPkgs.tasty)
            (hsPkgs.tasty-hedgehog)
            (hsPkgs.transformers)
            (hsPkgs.wallet-api)
            (hsPkgs.plutus-tx)
            (hsPkgs.lens)
            (hsPkgs.bytestring)
            (hsPkgs.aeson)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../wallet-api; }