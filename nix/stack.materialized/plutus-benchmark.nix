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
      identifier = { name = "plutus-benchmark"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "radu.ometita@iohk.io";
      author = "Radu Ometita";
      homepage = "https://github.com/iohk/plutus#readme";
      url = "";
      synopsis = "";
      description = "Please see the README on GitHub at <https://github.com/input-output-hk/plutus#readme>";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [
        "bench-validation/data/crowdfunding/*.plc"
        "bench-validation/data/future/*.plc"
        "bench-validation/data/multisigSM/*.plc"
        "bench-validation/data/vesting/*.plc"
        "bench-validation/data/marlowe/trustfund/*.plc"
        "bench-validation/data/marlowe/zerocoupon/*.plc"
        "templates/*.tpl"
        ];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
          (hsPkgs."plutus-tx-plugin" or (errorHandler.buildDepError "plutus-tx-plugin"))
          (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
          ];
        buildable = true;
        modules = [
          "Plutus/Benchmark/Clausify"
          "Plutus/Benchmark/Queens"
          "Plutus/Benchmark/Knights"
          "Plutus/Benchmark/Knights/ChessSetList"
          "Plutus/Benchmark/Knights/KnightHeuristic"
          "Plutus/Benchmark/Knights/Queue"
          "Plutus/Benchmark/Knights/Sort"
          "Plutus/Benchmark/Knights/Utils"
          "Plutus/Benchmark/LastPiece"
          "Plutus/Benchmark/Prime"
          ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "plutus-benchmark" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark" or (errorHandler.buildDepError "plutus-benchmark"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."plutus-tx-plugin" or (errorHandler.buildDepError "plutus-tx-plugin"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            ];
          buildable = true;
          hsSourceDirs = [ "app" ];
          mainPath = [ "Main.hs" ];
          };
        };
      benchmarks = {
        "large-plc-cek" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark" or (errorHandler.buildDepError "plutus-benchmark"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."plutus-tx-plugin" or (errorHandler.buildDepError "plutus-tx-plugin"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."criterion" or (errorHandler.buildDepError "criterion"))
            ];
          buildable = true;
          hsSourceDirs = [ "bench" ];
          };
        "validation" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."criterion" or (errorHandler.buildDepError "criterion"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            ];
          buildable = true;
          modules = [ "Paths_plutus_benchmark" ];
          hsSourceDirs = [ "bench-validation" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-benchmark;
    }