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
    flags = { development = false; };
    package = {
      specVersion = "2.0";
      identifier = { name = "byron-spec-ledger"; version = "0.1.0.0"; };
      license = "MIT";
      copyright = "";
      maintainer = "formal.methods@iohk.io";
      author = "IOHK Formal Methods Team";
      homepage = "https://github.com/input-output-hk/cardano-legder-specs";
      url = "";
      synopsis = "Executable specification of Cardano ledger";
      description = "";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [ "CHANGELOG.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bimap" or (errorHandler.buildDepError "bimap"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
          (hsPkgs."file-embed" or (errorHandler.buildDepError "file-embed"))
          (hsPkgs."goblins" or (errorHandler.buildDepError "goblins"))
          (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
          (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
          (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
          (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
          (hsPkgs."Unique" or (errorHandler.buildDepError "Unique"))
          (hsPkgs."cardano-binary" or (errorHandler.buildDepError "cardano-binary"))
          (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
          (hsPkgs."small-steps" or (errorHandler.buildDepError "small-steps"))
          ];
        buildable = true;
        modules = [
          "Hedgehog/Gen/Double"
          "Byron/Spec/Ledger/Core"
          "Byron/Spec/Ledger/Core/Generators"
          "Byron/Spec/Ledger/Core/Omniscient"
          "Byron/Spec/Ledger/Delegation"
          "Byron/Spec/Ledger/Delegation/Test"
          "Byron/Spec/Ledger/GlobalParams"
          "Byron/Spec/Ledger/Update"
          "Byron/Spec/Ledger/Update/Generators"
          "Byron/Spec/Ledger/Update/Test"
          "Byron/Spec/Ledger/UTxO"
          "Byron/Spec/Ledger/UTxO/Generators"
          "Byron/Spec/Ledger/Util"
          "Byron/Spec/Ledger/STS/UTXO"
          "Byron/Spec/Ledger/STS/UTXOW"
          "Byron/Spec/Ledger/STS/UTXOWS"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "doctests" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."doctest" or (errorHandler.buildDepError "doctest"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."small-steps" or (errorHandler.buildDepError "small-steps"))
            (hsPkgs."byron-spec-ledger" or (errorHandler.buildDepError "byron-spec-ledger"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.doctest-discover or (pkgs.buildPackages.doctest-discover or (errorHandler.buildToolDepError "doctest-discover")))
            ];
          buildable = true;
          hsSourceDirs = [ "test" ];
          mainPath = [ "DoctestDiscover.hs" ];
          };
        "byron-spec-ledger-test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bimap" or (errorHandler.buildDepError "bimap"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."tasty-hedgehog" or (errorHandler.buildDepError "tasty-hedgehog"))
            (hsPkgs."Unique" or (errorHandler.buildDepError "Unique"))
            (hsPkgs."byron-spec-ledger" or (errorHandler.buildDepError "byron-spec-ledger"))
            (hsPkgs."small-steps" or (errorHandler.buildDepError "small-steps"))
            ];
          buildable = true;
          modules = [
            "Test/Byron/Spec/Ledger/Core/Generators/Properties"
            "Test/Byron/Spec/Ledger/Delegation/Examples"
            "Test/Byron/Spec/Ledger/Delegation/Properties"
            "Test/Byron/Spec/Ledger/AbstractSize/Properties"
            "Test/Byron/Spec/Ledger/Update/Examples"
            "Test/Byron/Spec/Ledger/Update/Properties"
            "Test/Byron/Spec/Ledger/Relation/Properties"
            "Test/Byron/Spec/Ledger/UTxO/Properties"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/23; }