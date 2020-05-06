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
    flags = {};
    package = {
      specVersion = "2.2";
      identifier = { name = "plutus-contract"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "jann.mueller@iohk.io";
      author = "Jann Müller";
      homepage = "https://github.com/iohk/plutus#readme";
      url = "";
      synopsis = "";
      description = "Please see the README on GitHub at <https://github.com/input-output-hk/plutus#readme>";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
          (hsPkgs."plutus-emulator" or (buildDepError "plutus-emulator"))
          (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
          (hsPkgs."iots-export" or (buildDepError "iots-export"))
          (hsPkgs."aeson" or (buildDepError "aeson"))
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."servant" or (buildDepError "servant"))
          (hsPkgs."servant-server" or (buildDepError "servant-server"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."semigroupoids" or (buildDepError "semigroupoids"))
          (hsPkgs."profunctors" or (buildDepError "profunctors"))
          (hsPkgs."transformers" or (buildDepError "transformers"))
          (hsPkgs."warp" or (buildDepError "warp"))
          (hsPkgs."transformers-base" or (buildDepError "transformers-base"))
          (hsPkgs."monad-control" or (buildDepError "monad-control"))
          (hsPkgs."mmorph" or (buildDepError "mmorph"))
          (hsPkgs."row-types" or (buildDepError "row-types"))
          (hsPkgs."freer-simple" or (buildDepError "freer-simple"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          ];
        buildable = true;
        modules = [
          "Data/Row/Extras"
          "Language/Plutus/Contract"
          "Language/Plutus/Contract/App"
          "Language/Plutus/Contract/Effects/AwaitSlot"
          "Language/Plutus/Contract/Effects/AwaitTxConfirmed"
          "Language/Plutus/Contract/Effects/ExposeEndpoint"
          "Language/Plutus/Contract/Effects/OwnPubKey"
          "Language/Plutus/Contract/Effects/UtxoAt"
          "Language/Plutus/Contract/Effects/WatchAddress"
          "Language/Plutus/Contract/Effects/WriteTx"
          "Language/Plutus/Contract/Request"
          "Language/Plutus/Contract/Constraints"
          "Language/Plutus/Contract/Schema"
          "Language/Plutus/Contract/Trace"
          "Language/Plutus/Contract/Record"
          "Language/Plutus/Contract/IOTS"
          "Language/Plutus/Contract/Servant"
          "Language/Plutus/Contract/Resumable"
          "Language/Plutus/Contract/StateMachine"
          "Language/Plutus/Contract/StateMachine/OnChain"
          "Language/Plutus/Contract/Tx"
          "Language/Plutus/Contract/Util"
          "Language/Plutus/Contract/Wallet"
          "Language/Plutus/Contract/Typed/Tx"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "contract-doctests" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."containers" or (buildDepError "containers"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.unlit or (pkgs.buildPackages.unlit or (buildToolDepError "unlit")))
            (hsPkgs.buildPackages.doctest or (pkgs.buildPackages.doctest or (buildToolDepError "doctest")))
            ];
          buildable = true;
          modules = [ "ContractAPI" ];
          hsSourceDirs = [ "doctest" "doc" ];
          mainPath = [ "Main.hs" ];
          };
        "plutus-contract-test" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            (hsPkgs."extensible-effects" or (buildDepError "extensible-effects"))
            (hsPkgs."plutus-emulator" or (buildDepError "plutus-emulator"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            ];
          buildable = true;
          modules = [ "Spec/Rows" "Spec/State" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-contract;
    }