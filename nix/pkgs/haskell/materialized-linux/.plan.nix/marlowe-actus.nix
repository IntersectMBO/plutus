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
      identifier = { name = "marlowe-actus"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "dmytro.kondratiuk@iohk.io";
      author = "Dmytro Kondratiuk";
      homepage = "";
      url = "";
      synopsis = "Marlowe ACTUS: standardised financial contracts on Cardano Computation Layer";
      description = "implementation of ACTUS contracts on Marlowe";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [ "README.md" ];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."newtype-generics" or (errorHandler.buildDepError "newtype-generics"))
          (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
          (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
          (hsPkgs."plutus-contract" or (errorHandler.buildDepError "plutus-contract"))
          (hsPkgs."plutus-ledger" or (errorHandler.buildDepError "plutus-ledger"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
          (hsPkgs."marlowe" or (errorHandler.buildDepError "marlowe"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          (hsPkgs."sort" or (errorHandler.buildDepError "sort"))
          (hsPkgs."validation" or (errorHandler.buildDepError "validation"))
          ];
        buildable = true;
        modules = [
          "Language/Marlowe/ACTUS/MarloweCompat"
          "Language/Marlowe/ACTUS/Generator"
          "Language/Marlowe/ACTUS/Analysis"
          "Language/Marlowe/ACTUS/Ops"
          "Language/Marlowe/ACTUS/Definitions/BusinessEvents"
          "Language/Marlowe/ACTUS/Definitions/ContractTerms"
          "Language/Marlowe/ACTUS/Definitions/ContractState"
          "Language/Marlowe/ACTUS/Definitions/Schedule"
          "Language/Marlowe/ACTUS/Model/POF/PayoffModel"
          "Language/Marlowe/ACTUS/Model/POF/Payoff"
          "Language/Marlowe/ACTUS/Model/POF/PayoffFs"
          "Language/Marlowe/ACTUS/Model/STF/StateTransitionModel"
          "Language/Marlowe/ACTUS/Model/STF/StateTransition"
          "Language/Marlowe/ACTUS/Model/STF/StateTransitionFs"
          "Language/Marlowe/ACTUS/Model/SCHED/ContractScheduleModel"
          "Language/Marlowe/ACTUS/Model/SCHED/ContractSchedule"
          "Language/Marlowe/ACTUS/Model/INIT/StateInitializationModel"
          "Language/Marlowe/ACTUS/Model/APPLICABILITY/Applicability"
          "Language/Marlowe/ACTUS/Model/APPLICABILITY/ApplicabilityModel"
          "Language/Marlowe/ACTUS/Model/Utility/ANN/Annuity"
          "Language/Marlowe/ACTUS/Model/Utility/DateShift"
          "Language/Marlowe/ACTUS/Model/Utility/ScheduleGenerator"
          "Language/Marlowe/ACTUS/Model/Utility/YearFraction"
          ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "marlowe-shiny" = {
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
            (hsPkgs."inline-r" or (errorHandler.buildDepError "inline-r"))
            (hsPkgs."validation" or (errorHandler.buildDepError "validation"))
            ];
          buildable = true;
          modules = [
            "Language/Marlowe/ACTUS/MarloweCompat"
            "Language/Marlowe/ACTUS/Generator"
            "Language/Marlowe/ACTUS/Analysis"
            "Language/Marlowe/ACTUS/Definitions/BusinessEvents"
            "Language/Marlowe/ACTUS/Definitions/ContractTerms"
            "Language/Marlowe/ACTUS/Definitions/ContractState"
            "Language/Marlowe/ACTUS/Definitions/Schedule"
            "Language/Marlowe/ACTUS/Model/APPLICABILITY/Applicability"
            "Language/Marlowe/ACTUS/Model/APPLICABILITY/ApplicabilityModel"
            "Language/Marlowe/ACTUS/Model/POF/PayoffModel"
            "Language/Marlowe/ACTUS/Model/POF/Payoff"
            "Language/Marlowe/ACTUS/Model/POF/PayoffFs"
            "Language/Marlowe/ACTUS/Model/STF/StateTransitionModel"
            "Language/Marlowe/ACTUS/Model/STF/StateTransition"
            "Language/Marlowe/ACTUS/Model/STF/StateTransitionFs"
            "Language/Marlowe/ACTUS/Model/SCHED/ContractScheduleModel"
            "Language/Marlowe/ACTUS/Model/SCHED/ContractSchedule"
            "Language/Marlowe/ACTUS/Model/INIT/StateInitializationModel"
            "Language/Marlowe/ACTUS/Model/Utility/ANN/Annuity"
            "Language/Marlowe/ACTUS/Model/Utility/DateShift"
            "Language/Marlowe/ACTUS/Model/Utility/ScheduleGenerator"
            "Language/Marlowe/ACTUS/Model/Utility/YearFraction"
            "Language/Marlowe/ACTUS/Ops"
            ];
          hsSourceDirs = [ "app" "src" ];
          mainPath = [ "Main.hs" ];
          };
        "marlowe-actus-test-kit" = {
          depends = [
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."newtype-generics" or (errorHandler.buildDepError "newtype-generics"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."plutus-contract" or (errorHandler.buildDepError "plutus-contract"))
            (hsPkgs."plutus-ledger" or (errorHandler.buildDepError "plutus-ledger"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."marlowe" or (errorHandler.buildDepError "marlowe"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."sort" or (errorHandler.buildDepError "sort"))
            (hsPkgs."validation" or (errorHandler.buildDepError "validation"))
            (hsPkgs."servant" or (errorHandler.buildDepError "servant"))
            (hsPkgs."servant-client" or (errorHandler.buildDepError "servant-client"))
            (hsPkgs."http-client" or (errorHandler.buildDepError "http-client"))
            (hsPkgs."servant-client-core" or (errorHandler.buildDepError "servant-client-core"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            ];
          buildable = true;
          modules = [
            "Language/Marlowe/ACTUS/MarloweCompat"
            "Language/Marlowe/ACTUS/Generator"
            "Language/Marlowe/ACTUS/QCGenerator"
            "Language/Marlowe/ACTUS/Analysis"
            "Language/Marlowe/ACTUS/Definitions/BusinessEvents"
            "Language/Marlowe/ACTUS/Definitions/ContractTerms"
            "Language/Marlowe/ACTUS/Definitions/ContractState"
            "Language/Marlowe/ACTUS/Definitions/Schedule"
            "Language/Marlowe/ACTUS/Model/APPLICABILITY/Applicability"
            "Language/Marlowe/ACTUS/Model/APPLICABILITY/ApplicabilityModel"
            "Language/Marlowe/ACTUS/Model/POF/PayoffModel"
            "Language/Marlowe/ACTUS/Model/POF/Payoff"
            "Language/Marlowe/ACTUS/Model/POF/PayoffFs"
            "Language/Marlowe/ACTUS/Model/STF/StateTransitionModel"
            "Language/Marlowe/ACTUS/Model/STF/StateTransition"
            "Language/Marlowe/ACTUS/Model/STF/StateTransitionFs"
            "Language/Marlowe/ACTUS/Model/SCHED/ContractScheduleModel"
            "Language/Marlowe/ACTUS/Model/SCHED/ContractSchedule"
            "Language/Marlowe/ACTUS/Model/INIT/StateInitializationModel"
            "Language/Marlowe/ACTUS/Model/Utility/ANN/Annuity"
            "Language/Marlowe/ACTUS/Model/Utility/DateShift"
            "Language/Marlowe/ACTUS/Model/Utility/ScheduleGenerator"
            "Language/Marlowe/ACTUS/Model/Utility/YearFraction"
            "Language/Marlowe/ACTUS/Ops"
            ];
          hsSourceDirs = [ "testkit" "src" ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "marlowe-actus-test" = {
          depends = [
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."scientific" or (errorHandler.buildDepError "scientific"))
            (hsPkgs."extra" or (errorHandler.buildDepError "extra"))
            (hsPkgs."utf8-string" or (errorHandler.buildDepError "utf8-string"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            (hsPkgs."plutus-ledger" or (errorHandler.buildDepError "plutus-ledger"))
            (hsPkgs."plutus-contract" or (errorHandler.buildDepError "plutus-contract"))
            (hsPkgs."marlowe" or (errorHandler.buildDepError "marlowe"))
            (hsPkgs."marlowe-actus" or (errorHandler.buildDepError "marlowe-actus"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            (hsPkgs."marlowe" or (errorHandler.buildDepError "marlowe"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."validation" or (errorHandler.buildDepError "validation"))
            ];
          buildable = true;
          modules = [
            "Spec/Marlowe/ACTUS/Examples"
            "Spec/Marlowe/ACTUS/TestFramework"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../marlowe-actus; }