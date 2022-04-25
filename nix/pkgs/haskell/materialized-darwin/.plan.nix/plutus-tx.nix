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
      specVersion = "3.0";
      identifier = { name = "plutus-tx"; version = "1.0.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones";
      homepage = "";
      url = "";
      synopsis = "Libraries for Plutus Tx and its prelude";
      description = "Libraries for Plutus Tx and its prelude";
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
          (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
          (hsPkgs."flat" or (errorHandler.buildDepError "flat"))
          (hsPkgs."ghc-prim" or (errorHandler.buildDepError "ghc-prim"))
          (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
          (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
          (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
          (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
          (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
          (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."th-abstraction" or (errorHandler.buildDepError "th-abstraction"))
          (hsPkgs."th-compat" or (errorHandler.buildDepError "th-compat"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          ];
        buildable = true;
        modules = [
          "PlutusTx/IsData/Instances"
          "PlutusTx/IsData/TH"
          "PlutusTx/Lift/Instances"
          "PlutusTx/Lift/THUtils"
          "PlutusTx"
          "PlutusTx/Applicative"
          "PlutusTx/AssocMap"
          "PlutusTx/Base"
          "PlutusTx/Bool"
          "PlutusTx/Builtins"
          "PlutusTx/Builtins/Class"
          "PlutusTx/Builtins/Internal"
          "PlutusTx/Code"
          "PlutusTx/Coverage"
          "PlutusTx/Either"
          "PlutusTx/Enum"
          "PlutusTx/Eq"
          "PlutusTx/ErrorCodes"
          "PlutusTx/Foldable"
          "PlutusTx/Functor"
          "PlutusTx/Integer"
          "PlutusTx/IsData"
          "PlutusTx/IsData/Class"
          "PlutusTx/Lattice"
          "PlutusTx/Lift"
          "PlutusTx/Lift/Class"
          "PlutusTx/List"
          "PlutusTx/Maybe"
          "PlutusTx/Monoid"
          "PlutusTx/Numeric"
          "PlutusTx/Ord"
          "PlutusTx/Plugin/Utils"
          "PlutusTx/Prelude"
          "PlutusTx/Ratio"
          "PlutusTx/Semigroup"
          "PlutusTx/Sqrt"
          "PlutusTx/TH"
          "PlutusTx/These"
          "PlutusTx/Trace"
          "PlutusTx/Traversable"
          "PlutusTx/Utils"
          ];
        hsSourceDirs = [ "src" ];
        };
      sublibs = {
        "plutus-tx-testlib" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."flat" or (errorHandler.buildDepError "flat"))
            (hsPkgs."ghc-prim" or (errorHandler.buildDepError "ghc-prim"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."plutus-core".components.sublibs.plutus-core-testlib or (errorHandler.buildDepError "plutus-core:plutus-core-testlib"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."tagged" or (errorHandler.buildDepError "tagged"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            ];
          buildable = true;
          modules = [ "PlutusTx/Test" ];
          hsSourceDirs = [ "testlib" ];
          };
        };
      tests = {
        "plutus-tx-test" = {
          depends = [
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
            (hsPkgs."hedgehog-fn" or (errorHandler.buildDepError "hedgehog-fn"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."pretty-show" or (errorHandler.buildDepError "pretty-show"))
            (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hedgehog" or (errorHandler.buildDepError "tasty-hedgehog"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.doctest.components.exes.doctest or (pkgs.buildPackages.doctest or (errorHandler.buildToolDepError "doctest:doctest")))
            ];
          buildable = if compiler.isGhcjs && true || system.isWindows
            then false
            else true;
          modules = [
            "Suites/Laws"
            "Suites/Laws/Additive"
            "Suites/Laws/Construction"
            "Suites/Laws/Eq"
            "Suites/Laws/Helpers"
            "Suites/Laws/Module"
            "Suites/Laws/Multiplicative"
            "Suites/Laws/Ord"
            "Suites/Laws/Other"
            "Suites/Laws/Ring"
            "Suites/Laws/Serialization"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../plutus-tx; }