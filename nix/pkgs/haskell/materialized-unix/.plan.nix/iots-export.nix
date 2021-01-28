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
      specVersion = "1.12";
      identifier = { name = "iots-export"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "kris.jenkins@tweag.com";
      author = "Kris Jenkins";
      homepage = "";
      url = "";
      synopsis = "Tools to export Haskell to IOTS";
      description = "Tools to export Haskell to IOTS";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [
        "test/IOTS/fullContract.ts"
        "test/IOTS/functionList.ts"
        "test/IOTS/functionMaybe.ts"
        "test/IOTS/functionTuple.ts"
        "test/IOTS/response.ts"
        "test/IOTS/simpleSum.ts"
        "test/IOTS/singleFieldless.ts"
        "test/IOTS/tester.ts"
        "test/IOTS/thing.ts"
        "test/IOTS/user.ts"
        "test/IOTS/vestingTranche.ts"
        ];
      extraSrcFiles = [ "README.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."wl-pprint-text" or (errorHandler.buildDepError "wl-pprint-text"))
          (hsPkgs."tagged" or (errorHandler.buildDepError "tagged"))
          ];
        buildable = true;
        modules = [ "IOTS/Leijen" "IOTS/Tree" "IOTS" ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "iots-export-test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-golden" or (errorHandler.buildDepError "tasty-golden"))
            (hsPkgs."iots-export" or (errorHandler.buildDepError "iots-export"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."wl-pprint-text" or (errorHandler.buildDepError "wl-pprint-text"))
            ];
          buildable = true;
          modules = [ "IOTSSpec" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../iots-export; }