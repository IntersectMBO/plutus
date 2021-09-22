{ system
  , compiler
  , flags
  , pkgs
  , hsPkgs
  , pkgconfPkgs
  , errorHandler
  , config
  , ... }:
  ({
    flags = { release = false; };
    package = {
      specVersion = "1.12";
      identifier = { name = "cardano-addresses"; version = "3.6.0"; };
      license = "Apache-2.0";
      copyright = "2021 IOHK";
      maintainer = "operations@iohk.io";
      author = "IOHK";
      homepage = "https://github.com/input-output-hk/cardano-addresses#readme";
      url = "";
      synopsis = "Library utilities for mnemonic generation and address derivation.";
      description = "Please see the README on GitHub at <https://github.com/input-output-hk/cardano-addresses>";
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
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."base58-bytestring" or (errorHandler.buildDepError "base58-bytestring"))
          (hsPkgs."basement" or (errorHandler.buildDepError "basement"))
          (hsPkgs."bech32" or (errorHandler.buildDepError "bech32"))
          (hsPkgs."bech32-th" or (errorHandler.buildDepError "bech32-th"))
          (hsPkgs."binary" or (errorHandler.buildDepError "binary"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."cardano-crypto" or (errorHandler.buildDepError "cardano-crypto"))
          (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
          (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
          (hsPkgs."digest" or (errorHandler.buildDepError "digest"))
          (hsPkgs."either" or (errorHandler.buildDepError "either"))
          (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
          (hsPkgs."extra" or (errorHandler.buildDepError "extra"))
          (hsPkgs."fmt" or (errorHandler.buildDepError "fmt"))
          (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
          (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
          ] ++ (pkgs.lib).optional (compiler.isGhcjs && true || system.isGhcjs) (hsPkgs."cardano-addresses-jsbits" or (errorHandler.buildDepError "cardano-addresses-jsbits"));
        buildable = true;
        modules = [
          "Paths_cardano_addresses"
          "Cardano/Address"
          "Cardano/Address/Compat"
          "Cardano/Address/Derivation"
          "Cardano/Address/Internal"
          "Cardano/Address/Script"
          "Cardano/Address/Script/Parser"
          "Cardano/Address/Style/Byron"
          "Cardano/Address/Style/Icarus"
          "Cardano/Address/Style/Shared"
          "Cardano/Address/Style/Shelley"
          "Cardano/Codec/Bech32/Prefixes"
          "Cardano/Codec/Cbor"
          "Cardano/Mnemonic"
          "Codec/Binary/Encoding"
          "Data/Word7"
          ];
        hsSourceDirs = [ "lib" ];
        };
      tests = {
        "unit" = {
          depends = [
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."aeson-pretty" or (errorHandler.buildDepError "aeson-pretty"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bech32" or (errorHandler.buildDepError "bech32"))
            (hsPkgs."binary" or (errorHandler.buildDepError "binary"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."cardano-addresses" or (errorHandler.buildDepError "cardano-addresses"))
            (hsPkgs."cardano-crypto" or (errorHandler.buildDepError "cardano-crypto"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."hspec" or (errorHandler.buildDepError "hspec"))
            (hsPkgs."hspec-golden" or (errorHandler.buildDepError "hspec-golden"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."pretty-simple" or (errorHandler.buildDepError "pretty-simple"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.hspec-discover.components.exes.hspec-discover or (pkgs.buildPackages.hspec-discover or (errorHandler.buildToolDepError "hspec-discover:hspec-discover")))
            ];
          buildable = true;
          modules = [
            "AutoDiscover"
            "Cardano/Address/DerivationSpec"
            "Cardano/Address/Script/ParserSpec"
            "Cardano/Address/ScriptSpec"
            "Cardano/Address/Style/ByronSpec"
            "Cardano/Address/Style/IcarusSpec"
            "Cardano/Address/Style/SharedSpec"
            "Cardano/Address/Style/ShelleySpec"
            "Cardano/AddressSpec"
            "Cardano/Codec/CborSpec"
            "Cardano/MnemonicSpec"
            "Codec/Binary/EncodingSpec"
            "Data/Word7Spec"
            "Test/Arbitrary"
            "Paths_cardano_addresses"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "6";
      rev = "minimal";
      sha256 = "";
      }) // {
      url = "6";
      rev = "minimal";
      sha256 = "";
      };
    postUnpack = "sourceRoot+=/core; echo source root reset to \$sourceRoot";
    }) // { cabal-generator = "hpack"; }