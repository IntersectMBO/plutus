let
  buildDepError = pkg:
    builtins.throw ''
      The Haskell package set does not contain the package: ${pkg} (build dependency).
      
      If you are using Stackage, make sure that you are using a snapshot that contains the package. Otherwise you may need to update the Hackage snapshot you are using, usually by updating haskell.nix.
      '';
  sysDepError = pkg:
    builtins.throw ''
      The Nixpkgs package set does not contain the package: ${pkg} (system dependency).
      
      You may need to augment the system package mapping in haskell.nix so that it can be found.
      '';
  pkgConfDepError = pkg:
    builtins.throw ''
      The pkg-conf packages does not contain the package: ${pkg} (pkg-conf dependency).
      
      You may need to augment the pkg-conf package mapping in haskell.nix so that it can be found.
      '';
  exeDepError = pkg:
    builtins.throw ''
      The local executable components do not include the component: ${pkg} (executable dependency).
      '';
  legacyExeDepError = pkg:
    builtins.throw ''
      The Haskell package set does not contain the package: ${pkg} (executable dependency).
      
      If you are using Stackage, make sure that you are using a snapshot that contains the package. Otherwise you may need to update the Hackage snapshot you are using, usually by updating haskell.nix.
      '';
  buildToolDepError = pkg:
    builtins.throw ''
      Neither the Haskell package set or the Nixpkgs package set contain the package: ${pkg} (build tool dependency).
      
      If this is a system dependency:
      You may need to augment the system package mapping in haskell.nix so that it can be found.
      
      If this is a Haskell dependency:
      If you are using Stackage, make sure that you are using a snapshot that contains the package. Otherwise you may need to update the Hackage snapshot you are using, usually by updating haskell.nix.
      '';
in { system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { defer-plugin-errors = false; };
    package = {
      specVersion = "2.2";
      identifier = { name = "plutus-ledger"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones, Jann Mueller";
      homepage = "";
      url = "";
      synopsis = "Wallet API";
      description = "Plutus ledger library";
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
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."aeson" or (buildDepError "aeson"))
          (hsPkgs."base16-bytestring" or (buildDepError "base16-bytestring"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."cborg" or (buildDepError "cborg"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."cryptonite" or (buildDepError "cryptonite"))
          (hsPkgs."hashable" or (buildDepError "hashable"))
          (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
          (hsPkgs."iots-export" or (buildDepError "iots-export"))
          (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
          (hsPkgs."memory" or (buildDepError "memory"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."natural-transformation" or (buildDepError "natural-transformation"))
          (hsPkgs."operational" or (buildDepError "operational"))
          (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
          (hsPkgs."serialise" or (buildDepError "serialise"))
          (hsPkgs."servant" or (buildDepError "servant"))
          (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."transformers" or (buildDepError "transformers"))
          (hsPkgs."recursion-schemes" or (buildDepError "recursion-schemes"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."deriving-compat" or (buildDepError "deriving-compat"))
          (hsPkgs."newtype-generics" or (buildDepError "newtype-generics"))
          (hsPkgs."http-api-data" or (buildDepError "http-api-data"))
          (hsPkgs."cardano-crypto" or (buildDepError "cardano-crypto"))
          (hsPkgs."deepseq" or (buildDepError "deepseq"))
          (hsPkgs."freer-simple" or (buildDepError "freer-simple"))
          ];
        buildable = true;
        modules = [
          "Data/Aeson/Extras"
          "Data/Text/Prettyprint/Doc/Extras"
          "Ledger"
          "Ledger/Ada"
          "Ledger/Address"
          "Ledger/AddressMap"
          "Ledger/Blockchain"
          "Ledger/Constraints"
          "Ledger/Constraints/OffChain"
          "Ledger/Constraints/OnChain"
          "Ledger/Constraints/TxConstraints"
          "Ledger/Crypto"
          "Ledger/Generators"
          "Ledger/Oracle"
          "Ledger/Orphans"
          "Ledger/Slot"
          "Ledger/Scripts"
          "Ledger/Tx"
          "Ledger/TxId"
          "Ledger/Validation"
          "Ledger/Index"
          "Ledger/Interval"
          "Ledger/Value"
          "LedgerBytes"
          "Ledger/Tokens"
          "Ledger/Typed/Scripts"
          "Ledger/Typed/Scripts/Validators"
          "Ledger/Typed/Tx"
          "Ledger/Typed/TypeUtils"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "plutus-ledger-test" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hedgehog" or (buildDepError "tasty-hedgehog"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."aeson" or (buildDepError "aeson"))
            ];
          buildable = true;
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-ledger;
    }