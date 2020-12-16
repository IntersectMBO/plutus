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
      specVersion = "1.10";
      identifier = { name = "cardano-crypto-class"; version = "2.0.0"; };
      license = "Apache-2.0";
      copyright = "2019 IOHK";
      maintainer = "operations@iohk.io";
      author = "IOHK";
      homepage = "";
      url = "";
      synopsis = "Type classes abstracting over cryptography primitives for Cardano";
      description = "Type classes abstracting over cryptography primitives for Cardano";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [ "README.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."base16-bytestring" or (errorHandler.buildDepError "base16-bytestring"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."cardano-binary" or (errorHandler.buildDepError "cardano-binary"))
          (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
          (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
          (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
          (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
          (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
          ];
        buildable = true;
        modules = [
          "Cardano/Crypto/DSIGN"
          "Cardano/Crypto/Hash"
          "Cardano/Crypto/KES"
          "Cardano/Crypto/VRF"
          "Cardano/Crypto/DSIGN/Class"
          "Cardano/Crypto/DSIGN/Ed25519"
          "Cardano/Crypto/DSIGN/Ed448"
          "Cardano/Crypto/DSIGN/Mock"
          "Cardano/Crypto/DSIGN/NeverUsed"
          "Cardano/Crypto/DSIGN/RSAPSS"
          "Cardano/Crypto/Hash/Blake2b"
          "Cardano/Crypto/Hash/Class"
          "Cardano/Crypto/Hash/MD5"
          "Cardano/Crypto/Hash/NeverUsed"
          "Cardano/Crypto/Hash/SHA256"
          "Cardano/Crypto/Hash/Short"
          "Cardano/Crypto/KES/Class"
          "Cardano/Crypto/KES/Mock"
          "Cardano/Crypto/KES/NeverUsed"
          "Cardano/Crypto/KES/Simple"
          "Cardano/Crypto/Util"
          "Cardano/Crypto/VRF/Class"
          "Cardano/Crypto/VRF/Mock"
          "Cardano/Crypto/VRF/NeverUsed"
          "Cardano/Crypto/VRF/Simple"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "test-crypto" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."cardano-binary" or (errorHandler.buildDepError "cardano-binary"))
            (hsPkgs."cardano-crypto-class" or (errorHandler.buildDepError "cardano-crypto-class"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            ];
          buildable = true;
          modules = [
            "Test/Crypto/DSIGN"
            "Test/Crypto/Hash"
            "Test/Crypto/KES"
            "Test/Crypto/Orphans/Arbitrary"
            "Test/Crypto/Util"
            "Test/Crypto/VRF"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/6; }