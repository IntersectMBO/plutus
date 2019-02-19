{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "2.2";
      identifier = { name = "plutus-tutorial"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "jann.mueller@iohk.io";
      author = "Michael Peyton Jones, Jann Mueller";
      homepage = "";
      url = "";
      synopsis = "PlutusTx tutorial";
      description = "A tutorial for PlutusTx.";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.template-haskell)
          (hsPkgs.bytestring)
          (hsPkgs.language-plutus-core)
          (hsPkgs.plutus-tx)
          (hsPkgs.wallet-api)
          (hsPkgs.containers)
          ];
        build-tools = [ ((hsPkgs.buildPackages).doctest) ];
        };
      tests = {
        "tutorial-doctests" = {
          depends = [
            (hsPkgs.plutus-tutorial)
            (hsPkgs.base)
            (hsPkgs.template-haskell)
            (hsPkgs.bytestring)
            (hsPkgs.language-plutus-core)
            (hsPkgs.plutus-tx)
            (hsPkgs.wallet-api)
            (hsPkgs.containers)
            ];
          build-tools = [
            ((hsPkgs.buildPackages).markdown-unlit)
            ((hsPkgs.buildPackages).doctest)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../plutus-tutorial; }