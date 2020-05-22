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
      specVersion = "2.0";
      identifier = { name = "plutus-use-cases"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "jann.mueller@iohk.io";
      author = "Manuel M T Chakravarty, Jann Müller";
      homepage = "";
      url = "";
      synopsis = "Collection of smart contracts to develop the plutus/wallet interface";
      description = "Collection of smart contracts to develop the plutus/wallet interface.";
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
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."iots-export" or (buildDepError "iots-export"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
          (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
          (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
          (hsPkgs."playground-common" or (buildDepError "playground-common"))
          (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
          (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"));
        buildable = true;
        modules = [
          "Language/PlutusTx/Coordination/Contracts"
          "Language/PlutusTx/Coordination/Contracts/TokenAccount"
          "Language/PlutusTx/Coordination/Contracts/Crowdfunding"
          "Language/PlutusTx/Coordination/Contracts/Currency"
          "Language/PlutusTx/Coordination/Contracts/Escrow"
          "Language/PlutusTx/Coordination/Contracts/Future"
          "Language/PlutusTx/Coordination/Contracts/Game"
          "Language/PlutusTx/Coordination/Contracts/GameStateMachine"
          "Language/PlutusTx/Coordination/Contracts/ErrorHandling"
          "Language/PlutusTx/Coordination/Contracts/MultiSig"
          "Language/PlutusTx/Coordination/Contracts/MultiSigStateMachine"
          "Language/PlutusTx/Coordination/Contracts/PubKey"
          "Language/PlutusTx/Coordination/Contracts/Vesting"
          "Language/PlutusTx/Coordination/Contracts/Swap"
          ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "contract-guessing-game" = {
          depends = [
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-use-cases" or (buildDepError "plutus-use-cases"))
            (hsPkgs."base" or (buildDepError "base"))
            ];
          buildable = true;
          hsSourceDirs = [ "exe/game" ];
          mainPath = [ "Main.hs" ];
          };
        "contract-crowdfunding" = {
          depends = [
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-use-cases" or (buildDepError "plutus-use-cases"))
            (hsPkgs."base" or (buildDepError "base"))
            ];
          buildable = true;
          hsSourceDirs = [ "exe/crowdfunding" ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "plutus-use-cases-test" = {
          depends = [
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."plutus-use-cases" or (buildDepError "plutus-use-cases"))
            (hsPkgs."plutus-contract-tasty" or (buildDepError "plutus-contract-tasty"))
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."tasty-hedgehog" or (buildDepError "tasty-hedgehog"))
            (hsPkgs."tasty-golden" or (buildDepError "tasty-golden"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"));
          buildable = true;
          modules = [
            "Spec/Crowdfunding"
            "Spec/Currency"
            "Spec/ErrorHandling"
            "Spec/Escrow"
            "Spec/Future"
            "Spec/Game"
            "Spec/GameStateMachine"
            "Spec/Lib"
            "Spec/MultiSig"
            "Spec/MultiSigStateMachine"
            "Spec/PubKey"
            "Spec/Rollup"
            "Spec/TokenAccount"
            "Spec/Vesting"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      benchmarks = {
        "plutus-use-cases-bench" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."criterion" or (buildDepError "criterion"))
            (hsPkgs."cryptonite" or (buildDepError "cryptonite"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."memory" or (buildDepError "memory"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."plutus-use-cases" or (buildDepError "plutus-use-cases"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"));
          buildable = true;
          modules = [ "Scott" "Recursion" "IFix" "Opt" ];
          hsSourceDirs = [ "bench" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-use-cases;
    }