{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "2.2";
      identifier = { name = "plutus-contract-exe"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "jann.mueller@iohk.io";
      author = "Jann Müller";
      homepage = "https://github.com/iohk/plutus#readme";
      url = "";
      synopsis = "";
      description = "Please see the README on GitHub at <https://github.com/input-output-hk/plutus#readme>";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.wallet-api)
          (hsPkgs.aeson)
          (hsPkgs.base)
          (hsPkgs.text)
          ];
        };
      exes = {
        "contract-exe-guessing-game" = {
          depends = [
            (hsPkgs.plutus-contract-exe)
            (hsPkgs.plutus-use-cases)
            (hsPkgs.wallet-api)
            (hsPkgs.aeson)
            (hsPkgs.base)
            (hsPkgs.servant)
            (hsPkgs.servant-server)
            (hsPkgs.text)
            (hsPkgs.warp)
            (hsPkgs.lens)
            (hsPkgs.containers)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../plutus-contract-exe; }