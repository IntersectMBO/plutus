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
      identifier = { name = "cardano-ledger-pretty"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "formal.methods@iohk.io";
      author = "IOHK Formal Methods Team";
      homepage = "";
      url = "";
      synopsis = "";
      description = "Pretty Printers for the Cardano Ledger";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [ "README.md" "ChangeLog.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bech32" or (errorHandler.buildDepError "bech32"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."cardano-ledger-alonzo" or (errorHandler.buildDepError "cardano-ledger-alonzo"))
          (hsPkgs."cardano-ledger-shelley" or (errorHandler.buildDepError "cardano-ledger-shelley"))
          (hsPkgs."cardano-ledger-shelley-ma" or (errorHandler.buildDepError "cardano-ledger-shelley-ma"))
          (hsPkgs."cardano-crypto-class" or (errorHandler.buildDepError "cardano-crypto-class"))
          (hsPkgs."cardano-ledger-byron" or (errorHandler.buildDepError "cardano-ledger-byron"))
          (hsPkgs."cardano-protocol-tpraos" or (errorHandler.buildDepError "cardano-protocol-tpraos"))
          (hsPkgs."cardano-slotting" or (errorHandler.buildDepError "cardano-slotting"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."iproute" or (errorHandler.buildDepError "iproute"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."plutus-ledger-api" or (errorHandler.buildDepError "plutus-ledger-api"))
          (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
          (hsPkgs."small-steps" or (errorHandler.buildDepError "small-steps"))
          (hsPkgs."cardano-ledger-core" or (errorHandler.buildDepError "cardano-ledger-core"))
          (hsPkgs."strict-containers" or (errorHandler.buildDepError "strict-containers"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          ];
        buildable = true;
        modules = [
          "Cardano/Ledger/Pretty"
          "Cardano/Ledger/Pretty/Alonzo"
          "Cardano/Ledger/Pretty/Mary"
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
    postUnpack = "sourceRoot+=/libs/cardano-ledger-pretty; echo source root reset to \$sourceRoot";
    }