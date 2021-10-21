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
    flags = {};
    package = {
      specVersion = "2.2";
      identifier = { name = "shelley-spec-ledger-test"; version = "0.1.0.0"; };
      license = "Apache-2.0";
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
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."cardano-ledger-shelley-test" or (errorHandler.buildDepError "cardano-ledger-shelley-test"))
          ];
        buildable = true;
        modules = [
          "Test/Shelley/Spec/Ledger/BenchmarkFunctions"
          "Test/Shelley/Spec/Ledger/ConcreteCryptoTypes"
          "Test/Shelley/Spec/Ledger/Examples/Cast"
          "Test/Shelley/Spec/Ledger/Examples/Consensus"
          "Test/Shelley/Spec/Ledger/Generator/Block"
          "Test/Shelley/Spec/Ledger/Generator/Constants"
          "Test/Shelley/Spec/Ledger/Generator/Core"
          "Test/Shelley/Spec/Ledger/Generator/Delegation"
          "Test/Shelley/Spec/Ledger/Generator/Metadata"
          "Test/Shelley/Spec/Ledger/Generator/Presets"
          "Test/Shelley/Spec/Ledger/Generator/Trace/Chain"
          "Test/Shelley/Spec/Ledger/Generator/Trace/DCert"
          "Test/Shelley/Spec/Ledger/Generator/Trace/Ledger"
          "Test/Shelley/Spec/Ledger/Generator/Update"
          "Test/Shelley/Spec/Ledger/Generator/Utxo"
          "Test/Shelley/Spec/Ledger/Generator/EraGen"
          "Test/Shelley/Spec/Ledger/Generator/ScriptClass"
          "Test/Shelley/Spec/Ledger/Generator/ShelleyEraGen"
          "Test/Shelley/Spec/Ledger/Orphans"
          "Test/Shelley/Spec/Ledger/Rules/ClassifyTraces"
          "Test/Shelley/Spec/Ledger/Rules/TestChain"
          "Test/Shelley/Spec/Ledger/Serialisation/CDDLUtils"
          "Test/Shelley/Spec/Ledger/Serialisation/Generators"
          "Test/Shelley/Spec/Ledger/Serialisation/EraIndepGenerators"
          "Test/Shelley/Spec/Ledger/Serialisation/Generators/Bootstrap"
          "Test/Shelley/Spec/Ledger/Serialisation/Generators/Genesis"
          "Test/Shelley/Spec/Ledger/Serialisation/GoldenUtils"
          "Test/Shelley/Spec/Ledger/Shrinkers"
          "Test/Shelley/Spec/Ledger/Utils"
          "Test/Shelley/Spec/Ledger/PropertyTests"
          ];
        hsSourceDirs = [ "src" ];
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "10";
      rev = "minimal";
      sha256 = "";
      }) // {
      url = "10";
      rev = "minimal";
      sha256 = "";
      };
    postUnpack = "sourceRoot+=/shelley/chain-and-ledger/shelley-spec-ledger-test; echo source root reset to \$sourceRoot";
    }