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
      identifier = { name = "shelley-spec-ledger"; version = "0.1.0.0"; };
      license = "NONE";
      copyright = "";
      maintainer = "formal.methods@iohk.io";
      author = "IOHK Formal Methods Team";
      homepage = "";
      url = "";
      synopsis = "";
      description = "Shelley Ledger Executable Model";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [
        "cddl-files/shelley.cddl"
        "cddl-files/mock/crypto.cddl"
        "cddl-files/mock/extras.cddl"
        ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
          (hsPkgs."cborg-json" or (errorHandler.buildDepError "cborg-json"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
          (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
          (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
          (hsPkgs."small-steps" or (errorHandler.buildDepError "small-steps"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."shelley-spec-non-integral" or (errorHandler.buildDepError "shelley-spec-non-integral"))
          (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          (hsPkgs."byron-spec-ledger" or (errorHandler.buildDepError "byron-spec-ledger"))
          (hsPkgs."cardano-binary" or (errorHandler.buildDepError "cardano-binary"))
          (hsPkgs."cardano-crypto-class" or (errorHandler.buildDepError "cardano-crypto-class"))
          (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
          (hsPkgs."cardano-slotting" or (errorHandler.buildDepError "cardano-slotting"))
          ];
        buildable = true;
        modules = [
          "Shelley/Spec/Ledger/API/Validation"
          "Shelley/Spec/Ledger/API/Mempool"
          "Shelley/Spec/Ledger/API/Protocol"
          "Shelley/Spec/Ledger/API/Wallet"
          "Shelley/Spec/Ledger/Address"
          "Shelley/Spec/Ledger/BaseTypes"
          "Shelley/Spec/Ledger/BlockChain"
          "Shelley/Spec/Ledger/Coin"
          "Shelley/Spec/Ledger/Keys"
          "Shelley/Spec/Ledger/UTxO"
          "Shelley/Spec/Ledger/Slot"
          "Shelley/Spec/Ledger/PParams"
          "Shelley/Spec/Ledger/Rewards"
          "Shelley/Spec/Ledger/EpochBoundary"
          "Shelley/Spec/Ledger/LedgerState"
          "Shelley/Spec/Ledger/MetaData"
          "Shelley/Spec/Ledger/Serialization"
          "Shelley/Spec/Ledger/Delegation/PoolParams"
          "Shelley/Spec/Ledger/Delegation/Certificates"
          "Shelley/Spec/Ledger/OCert"
          "Shelley/Spec/Ledger/Tx"
          "Shelley/Spec/Ledger/TxData"
          "Shelley/Spec/Ledger/Validation"
          "Shelley/Spec/Ledger/Scripts"
          "Shelley/Spec/Ledger/STS/Bbody"
          "Shelley/Spec/Ledger/STS/Tick"
          "Shelley/Spec/Ledger/STS/Chain"
          "Shelley/Spec/Ledger/STS/Deleg"
          "Shelley/Spec/Ledger/STS/Delegs"
          "Shelley/Spec/Ledger/STS/Delpl"
          "Shelley/Spec/Ledger/STS/Epoch"
          "Shelley/Spec/Ledger/STS/Ledger"
          "Shelley/Spec/Ledger/STS/Ledgers"
          "Shelley/Spec/Ledger/STS/Mir"
          "Shelley/Spec/Ledger/STS/NewEpoch"
          "Shelley/Spec/Ledger/STS/Newpp"
          "Shelley/Spec/Ledger/STS/Ocert"
          "Shelley/Spec/Ledger/STS/Overlay"
          "Shelley/Spec/Ledger/STS/Pool"
          "Shelley/Spec/Ledger/STS/PoolReap"
          "Shelley/Spec/Ledger/STS/Ppup"
          "Shelley/Spec/Ledger/STS/Prtcl"
          "Shelley/Spec/Ledger/STS/Rupd"
          "Shelley/Spec/Ledger/STS/Snap"
          "Shelley/Spec/Ledger/STS/Updn"
          "Shelley/Spec/Ledger/STS/Utxo"
          "Shelley/Spec/Ledger/STS/Utxow"
          "Shelley/Spec/Ledger/Crypto"
          "Shelley/Spec/Ledger/API"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "shelley-spec-ledger-test" = {
          depends = [
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."base16-bytestring" or (errorHandler.buildDepError "base16-bytestring"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."cardano-binary" or (errorHandler.buildDepError "cardano-binary"))
            (hsPkgs."cardano-crypto-class" or (errorHandler.buildDepError "cardano-crypto-class"))
            (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
            (hsPkgs."cardano-slotting" or (errorHandler.buildDepError "cardano-slotting"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            (hsPkgs."byron-spec-ledger" or (errorHandler.buildDepError "byron-spec-ledger"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
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
            "Test/Shelley/Spec/Ledger/Utils"
            "Test/Shelley/Spec/Ledger/ConcreteCryptoTypes"
            "Test/Cardano/Crypto/VRF/Fake"
            "Test/Shelley/Spec/Ledger/PreSTSMutator"
            "Test/Shelley/Spec/Ledger/PreSTSGenerator"
            "Test/Shelley/Spec/Ledger/Generator/Constants"
            "Test/Shelley/Spec/Ledger/Generator/Block"
            "Test/Shelley/Spec/Ledger/Generator/Core"
            "Test/Shelley/Spec/Ledger/Generator/Trace/Chain"
            "Test/Shelley/Spec/Ledger/Generator/Trace/Ledger"
            "Test/Shelley/Spec/Ledger/Generator/Trace/DCert"
            "Test/Shelley/Spec/Ledger/Generator/Delegation"
            "Test/Shelley/Spec/Ledger/Generator/Presets"
            "Test/Shelley/Spec/Ledger/Generator/Update"
            "Test/Shelley/Spec/Ledger/Generator/Utxo"
            "Test/Shelley/Spec/Ledger/PropertyTests"
            "Test/Shelley/Spec/Ledger/Shrinkers"
            "Test/Shelley/Spec/Ledger/Examples/STSTests"
            "Test/Shelley/Spec/Ledger/Examples/Examples"
            "Test/Shelley/Spec/Ledger/Examples/MultiSigExamples"
            "Test/Shelley/Spec/Ledger/Examples/UnitTests"
            "Test/Shelley/Spec/Ledger/Rules/ClassifyTraces"
            "Test/Shelley/Spec/Ledger/Rules/TestChain"
            "Test/Shelley/Spec/Ledger/Rules/TestDeleg"
            "Test/Shelley/Spec/Ledger/Rules/TestLedger"
            "Test/Shelley/Spec/Ledger/Rules/TestNewEpoch"
            "Test/Shelley/Spec/Ledger/Rules/TestDelegs"
            "Test/Shelley/Spec/Ledger/Rules/TestPool"
            "Test/Shelley/Spec/Ledger/Rules/TestPoolreap"
            "Test/Shelley/Spec/Ledger/Rules/TestUtxo"
            "Test/Shelley/Spec/Ledger/Rules/TestUtxow"
            "Test/Shelley/Spec/Ledger/Examples/Serialization"
            "Test/Shelley/Spec/Ledger/Examples/CDDL"
            "Test/Shelley/Spec/Ledger/Examples/Fees"
            "Test/TestScenario"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Tests.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/26; }