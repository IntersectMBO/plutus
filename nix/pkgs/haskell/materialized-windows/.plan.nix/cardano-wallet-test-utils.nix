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
    flags = { release = false; };
    package = {
      specVersion = "1.10";
      identifier = {
        name = "cardano-wallet-test-utils";
        version = "2021.9.29";
        };
      license = "Apache-2.0";
      copyright = "2018-2020 IOHK";
      maintainer = "operations@iohk.io";
      author = "IOHK Engineering Team";
      homepage = "https://github.com/input-output-hk/cardano-wallet";
      url = "";
      synopsis = "Shared utilities for writing unit and property tests.";
      description = "Shared utilities for writing unit and property tests.";
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
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
          (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
          (hsPkgs."file-embed" or (errorHandler.buildDepError "file-embed"))
          (hsPkgs."formatting" or (errorHandler.buildDepError "formatting"))
          (hsPkgs."hspec" or (errorHandler.buildDepError "hspec"))
          (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
          (hsPkgs."either" or (errorHandler.buildDepError "either"))
          (hsPkgs."fmt" or (errorHandler.buildDepError "fmt"))
          (hsPkgs."hspec-core" or (errorHandler.buildDepError "hspec-core"))
          (hsPkgs."hspec-expectations" or (errorHandler.buildDepError "hspec-expectations"))
          (hsPkgs."hspec-golden-aeson" or (errorHandler.buildDepError "hspec-golden-aeson"))
          (hsPkgs."http-api-data" or (errorHandler.buildDepError "http-api-data"))
          (hsPkgs."HUnit" or (errorHandler.buildDepError "HUnit"))
          (hsPkgs."iohk-monitoring" or (errorHandler.buildDepError "iohk-monitoring"))
          (hsPkgs."int-cast" or (errorHandler.buildDepError "int-cast"))
          (hsPkgs."lattices" or (errorHandler.buildDepError "lattices"))
          (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
          (hsPkgs."pretty-simple" or (errorHandler.buildDepError "pretty-simple"))
          (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
          (hsPkgs."quickcheck-classes" or (errorHandler.buildDepError "quickcheck-classes"))
          (hsPkgs."say" or (errorHandler.buildDepError "say"))
          (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."text-class" or (errorHandler.buildDepError "text-class"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          (hsPkgs."unliftio" or (errorHandler.buildDepError "unliftio"))
          (hsPkgs."unliftio-core" or (errorHandler.buildDepError "unliftio-core"))
          (hsPkgs."wai-app-static" or (errorHandler.buildDepError "wai-app-static"))
          (hsPkgs."warp" or (errorHandler.buildDepError "warp"))
          ];
        buildable = true;
        modules = [
          "Test/Hspec/Extra"
          "Test/Hspec/Goldens"
          "Test/QuickCheck/Extra"
          "Test/Utils/Env"
          "Test/Utils/FilePath"
          "Test/Utils/Laws"
          "Test/Utils/Laws/PartialOrd"
          "Test/Utils/Paths"
          "Test/Utils/Pretty"
          "Test/Utils/Roundtrip"
          "Test/Utils/Resource"
          "Test/Utils/Platform"
          "Test/Utils/Startup"
          "Test/Utils/StaticServer"
          "Test/Utils/Time"
          "Test/Utils/Trace"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "unit" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."cardano-wallet-test-utils" or (errorHandler.buildDepError "cardano-wallet-test-utils"))
            (hsPkgs."fmt" or (errorHandler.buildDepError "fmt"))
            (hsPkgs."hspec" or (errorHandler.buildDepError "hspec"))
            (hsPkgs."hspec-core" or (errorHandler.buildDepError "hspec-core"))
            (hsPkgs."hspec-expectations-lifted" or (errorHandler.buildDepError "hspec-expectations-lifted"))
            (hsPkgs."silently" or (errorHandler.buildDepError "silently"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."unliftio" or (errorHandler.buildDepError "unliftio"))
            (hsPkgs."unliftio-core" or (errorHandler.buildDepError "unliftio-core"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.hspec-discover.components.exes.hspec-discover or (pkgs.buildPackages.hspec-discover or (errorHandler.buildToolDepError "hspec-discover:hspec-discover")))
            ];
          buildable = true;
          modules = [ "Test/Hspec/ExtraSpec" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "7";
      rev = "minimal";
      sha256 = "";
      }) // {
      url = "7";
      rev = "minimal";
      sha256 = "";
      };
    postUnpack = "sourceRoot+=/lib/test-utils; echo source root reset to \$sourceRoot";
    }