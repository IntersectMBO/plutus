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
      identifier = { name = "plutus-tx"; version = "0.1.0.0"; };
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
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [ "README.md" ];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
          (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
          (hsPkgs."th-abstraction" or (errorHandler.buildDepError "th-abstraction"))
          (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
          (hsPkgs."flat" or (errorHandler.buildDepError "flat"))
          (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
          (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
          (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
          (hsPkgs."ghc-prim" or (errorHandler.buildDepError "ghc-prim"))
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          ];
        build-tools = [
          (hsPkgs.buildPackages.doctest or (pkgs.buildPackages.doctest or (errorHandler.buildToolDepError "doctest")))
          ];
        buildable = true;
        modules = [
          "Language/PlutusTx/IsData/Instances"
          "Language/PlutusTx/IsData/TH"
          "Language/PlutusTx/Lift/THUtils"
          "Language/PlutusTx/Lift/Instances"
          "Language/PlutusTx"
          "Language/PlutusTx/TH"
          "Language/PlutusTx/Prelude"
          "Language/PlutusTx/Evaluation"
          "Language/PlutusTx/Applicative"
          "Language/PlutusTx/Bool"
          "Language/PlutusTx/IsData"
          "Language/PlutusTx/IsData/Class"
          "Language/PlutusTx/Eq"
          "Language/PlutusTx/Functor"
          "Language/PlutusTx/Lattice"
          "Language/PlutusTx/List"
          "Language/PlutusTx/Ord"
          "Language/PlutusTx/Maybe"
          "Language/PlutusTx/Numeric"
          "Language/PlutusTx/Ratio"
          "Language/PlutusTx/Semigroup"
          "Language/PlutusTx/Monoid"
          "Language/PlutusTx/AssocMap"
          "Language/PlutusTx/These"
          "Language/PlutusTx/Code"
          "Language/PlutusTx/Data"
          "Language/PlutusTx/Lift"
          "Language/PlutusTx/Lift/Class"
          "Language/PlutusTx/Builtins"
          "Language/PlutusTx/Plugin/Utils"
          "Language/PlutusTx/Utils"
          "Language/PlutusTx/String"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "plutus-tx-test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."tasty-hedgehog" or (errorHandler.buildDepError "tasty-hedgehog"))
            (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            ];
          buildable = true;
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../plutus-tx; }