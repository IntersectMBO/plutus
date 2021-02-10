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
      specVersion = "1.8";
      identifier = { name = "shelley-spec-ledger-test"; version = "0.1.0.0"; };
      license = "NONE";
      copyright = "";
      maintainer = "formal.methods@iohk.io";
      author = "IOHK Formal Methods Team";
      homepage = "";
      url = "";
      synopsis = "";
      description = "Test helpers from shelley-spec-ledger exposed to other packages";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."cardano-binary" or (errorHandler.buildDepError "cardano-binary"))
          (hsPkgs."cardano-crypto-class" or (errorHandler.buildDepError "cardano-crypto-class"))
          (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
          (hsPkgs."cardano-slotting" or (errorHandler.buildDepError "cardano-slotting"))
          (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
          (hsPkgs."byron-spec-ledger" or (errorHandler.buildDepError "byron-spec-ledger"))
          (hsPkgs."shelley-spec-ledger" or (errorHandler.buildDepError "shelley-spec-ledger"))
          (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
          (hsPkgs."multiset" or (errorHandler.buildDepError "multiset"))
          (hsPkgs."process-extras" or (errorHandler.buildDepError "process-extras"))
          (hsPkgs."small-steps" or (errorHandler.buildDepError "small-steps"))
          (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
          (hsPkgs."tasty-hedgehog" or (errorHandler.buildDepError "tasty-hedgehog"))
          (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
          (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          ];
        buildable = true;
        modules = [
          "Test/Cardano/Crypto/VRF/Fake"
          "Test/Shelley/Spec/Ledger/ConcreteCryptoTypes"
          "Test/Shelley/Spec/Ledger/Examples/Examples"
          "Test/Shelley/Spec/Ledger/Examples/MultiSigExamples"
          "Test/Shelley/Spec/Ledger/Examples/Serialization"
          "Test/Shelley/Spec/Ledger/Generator/Block"
          "Test/Shelley/Spec/Ledger/Generator/Constants"
          "Test/Shelley/Spec/Ledger/Generator/Core"
          "Test/Shelley/Spec/Ledger/Generator/Delegation"
          "Test/Shelley/Spec/Ledger/Generator/Presets"
          "Test/Shelley/Spec/Ledger/Generator/Trace/Chain"
          "Test/Shelley/Spec/Ledger/Generator/Trace/DCert"
          "Test/Shelley/Spec/Ledger/Generator/Trace/Ledger"
          "Test/Shelley/Spec/Ledger/Generator/Update"
          "Test/Shelley/Spec/Ledger/Generator/Utxo"
          "Test/Shelley/Spec/Ledger/PreSTSGenerator"
          "Test/Shelley/Spec/Ledger/PreSTSMutator"
          "Test/Shelley/Spec/Ledger/Shrinkers"
          "Test/Shelley/Spec/Ledger/Utils"
          ];
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/27; }