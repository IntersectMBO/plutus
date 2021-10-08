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
      dataDir = ".";
      dataFiles = [ "common/templates/*.tpl" "validation/data/*.flat" ];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      sublibs = {
        "plutus-benchmark-common" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."criterion" or (errorHandler.buildDepError "criterion"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."flat" or (errorHandler.buildDepError "flat"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            ];
          buildable = true;
          modules = [
            "Paths_plutus_benchmark"
            "PlutusBenchmark/Common"
            "PlutusBenchmark/NaturalSort"
            ];
          hsSourceDirs = [ "common" ];
          };
        "nofib-internal" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."plutus-tx-plugin" or (errorHandler.buildDepError "plutus-tx-plugin"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            ];
          buildable = true;
          modules = [
            "PlutusBenchmark/NoFib/Clausify"
            "PlutusBenchmark/NoFib/Queens"
            "PlutusBenchmark/NoFib/Knights"
            "PlutusBenchmark/NoFib/Knights/ChessSetList"
            "PlutusBenchmark/NoFib/Knights/KnightHeuristic"
            "PlutusBenchmark/NoFib/Knights/Queue"
            "PlutusBenchmark/NoFib/Knights/Sort"
            "PlutusBenchmark/NoFib/Knights/Utils"
            "PlutusBenchmark/NoFib/LastPiece"
            "PlutusBenchmark/NoFib/Prime"
            ];
          hsSourceDirs = [ "nofib/src" ];
          };
        "list-sort-internal" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."plutus-tx-plugin" or (errorHandler.buildDepError "plutus-tx-plugin"))
            ];
          buildable = true;
          modules = [
            "PlutusBenchmark/ListSort/GhcSort"
            "PlutusBenchmark/ListSort/InsertionSort"
            "PlutusBenchmark/ListSort/MergeSort"
            "PlutusBenchmark/ListSort/QuickSort"
            ];
          hsSourceDirs = [ "list-sort/src" ];
          };
        };
      exes = {
        "nofib-exe" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-benchmark".components.sublibs.nofib-internal or (errorHandler.buildDepError "plutus-benchmark:nofib-internal"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."ansi-wl-pprint" or (errorHandler.buildDepError "ansi-wl-pprint"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."flat" or (errorHandler.buildDepError "flat"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            ];
          buildable = true;
          hsSourceDirs = [ "nofib/exe" ];
          mainPath = [ "Main.hs" ];
          };
        "list-sort-exe" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-benchmark".components.sublibs.list-sort-internal or (errorHandler.buildDepError "plutus-benchmark:list-sort-internal"))
            (hsPkgs."monoidal-containers" or (errorHandler.buildDepError "monoidal-containers"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            ];
          buildable = true;
          hsSourceDirs = [ "list-sort/exe" ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "plutus-benchmark-nofib-tests" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-benchmark".components.sublibs.nofib-internal or (errorHandler.buildDepError "plutus-benchmark:nofib-internal"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            ];
          buildable = true;
          hsSourceDirs = [ "nofib/test" ];
          mainPath = [ "Spec.hs" ];
          };
        "plutus-benchmark-list-sort-tests" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-benchmark".components.sublibs.list-sort-internal or (errorHandler.buildDepError "plutus-benchmark:list-sort-internal"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            ];
          buildable = true;
          hsSourceDirs = [ "list-sort/test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      benchmarks = {
        "nofib" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-benchmark".components.sublibs.nofib-internal or (errorHandler.buildDepError "plutus-benchmark:nofib-internal"))
            (hsPkgs."criterion" or (errorHandler.buildDepError "criterion"))
            ];
          buildable = true;
          modules = [ "Shared" ];
          hsSourceDirs = [ "nofib/bench" ];
          };
        "nofib-hs" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-benchmark".components.sublibs.nofib-internal or (errorHandler.buildDepError "plutus-benchmark:nofib-internal"))
            (hsPkgs."criterion" or (errorHandler.buildDepError "criterion"))
            ];
          buildable = true;
          modules = [ "Shared" ];
          hsSourceDirs = [ "nofib/bench" ];
          };
        "list-sort" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-benchmark".components.sublibs.list-sort-internal or (errorHandler.buildDepError "plutus-benchmark:list-sort-internal"))
            (hsPkgs."criterion" or (errorHandler.buildDepError "criterion"))
            ];
          buildable = true;
          hsSourceDirs = [ "list-sort/bench" ];
          };
        "validation" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-benchmark".components.sublibs.plutus-benchmark-common or (errorHandler.buildDepError "plutus-benchmark:plutus-benchmark-common"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."criterion" or (errorHandler.buildDepError "criterion"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."flat" or (errorHandler.buildDepError "flat"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            ];
          buildable = true;
          hsSourceDirs = [ "validation" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../plutus-benchmark; }