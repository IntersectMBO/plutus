{ system
  , compiler
  , flags
  , pkgs
  , hsPkgs
  , pkgconfPkgs
  , errorHandler
  , config
  , ... }:
  {
    flags = { defer-plugin-errors = false; };
    package = {
      specVersion = "2.2";
      identifier = { name = "marlowe-actus-theory"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "dmytro.kondratiuk@iohk.io";
      author = "Dmytro Kondratiuk";
      homepage = "";
      url = "";
      synopsis = "Marlowe ACTUS theory: formalisations of ACTUS standard";
      description = "Provides a generator of ACTUS-definitions for Agda";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [ "README.md" ];
      };
    components = {
      exes = {
        "actus-agda-gen" = {
          depends = [
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."deriving-aeson" or (errorHandler.buildDepError "deriving-aeson"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."newtype-generics" or (errorHandler.buildDepError "newtype-generics"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."plutus-contract" or (errorHandler.buildDepError "plutus-contract"))
            (hsPkgs."plutus-ledger" or (errorHandler.buildDepError "plutus-ledger"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."sbv" or (errorHandler.buildDepError "sbv"))
            (hsPkgs."wl-pprint" or (errorHandler.buildDepError "wl-pprint"))
            (hsPkgs."freer-simple" or (errorHandler.buildDepError "freer-simple"))
            (hsPkgs."marlowe" or (errorHandler.buildDepError "marlowe"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."loch-th" or (errorHandler.buildDepError "loch-th"))
            (hsPkgs."sort" or (errorHandler.buildDepError "sort"))
            (hsPkgs."Agda" or (errorHandler.buildDepError "Agda"))
            (hsPkgs."pretty" or (errorHandler.buildDepError "pretty"))
            (hsPkgs."marlowe-actus" or (errorHandler.buildDepError "marlowe-actus"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.unlit or (pkgs.buildPackages.unlit or (errorHandler.buildToolDepError "unlit")))
            ];
          buildable = true;
          modules = [
            "Language/Marlowe/ACTUS/Agda/AgdaOps"
            "Language/Marlowe/ACTUS/Agda/AgdaGen"
            "Language/Marlowe/ACTUS/Agda/GenPayoff"
            "Language/Marlowe/ACTUS/Agda/GenStateTransition"
            ];
          hsSourceDirs = [ "app" "src" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./marlowe-actus-theory;
    }