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
      identifier = { name = "plutus-playground-server"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "kris.jenkins@tweag.io";
      author = "Kris Jenkins";
      homepage = "https://github.com/iohk/plutus#readme";
      url = "";
      synopsis = "";
      description = "Please see the README on GitHub at <https://github.com/input-output-hk/plutus#readme>";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [
        "usecases/Crowdfunding.hs"
        "usecases/ErrorHandling.hs"
        "usecases/Game.hs"
        "usecases/Vesting.hs"
        "usecases/Starter.hs"
        "test/gists1.json"
        ];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."aeson" or (buildDepError "aeson"))
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."cookie" or (buildDepError "cookie"))
          (hsPkgs."cryptonite" or (buildDepError "cryptonite"))
          (hsPkgs."exceptions" or (buildDepError "exceptions"))
          (hsPkgs."file-embed" or (buildDepError "file-embed"))
          (hsPkgs."filepath" or (buildDepError "filepath"))
          (hsPkgs."http-client" or (buildDepError "http-client"))
          (hsPkgs."http-client-tls" or (buildDepError "http-client-tls"))
          (hsPkgs."http-conduit" or (buildDepError "http-conduit"))
          (hsPkgs."http-types" or (buildDepError "http-types"))
          (hsPkgs."iots-export" or (buildDepError "iots-export"))
          (hsPkgs."jwt" or (buildDepError "jwt"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."monad-logger" or (buildDepError "monad-logger"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."newtype-generics" or (buildDepError "newtype-generics"))
          (hsPkgs."playground-common" or (buildDepError "playground-common"))
          (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
          (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
          (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
          (hsPkgs."process" or (buildDepError "process"))
          (hsPkgs."regex-compat" or (buildDepError "regex-compat"))
          (hsPkgs."recursion-schemes" or (buildDepError "recursion-schemes"))
          (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
          (hsPkgs."row-types" or (buildDepError "row-types"))
          (hsPkgs."serialise" or (buildDepError "serialise"))
          (hsPkgs."servant" or (buildDepError "servant"))
          (hsPkgs."servant-client" or (buildDepError "servant-client"))
          (hsPkgs."servant-client-core" or (buildDepError "servant-client-core"))
          (hsPkgs."servant-purescript" or (buildDepError "servant-purescript"))
          (hsPkgs."servant-server" or (buildDepError "servant-server"))
          (hsPkgs."temporary" or (buildDepError "temporary"))
          (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."time" or (buildDepError "time"))
          (hsPkgs."time-units" or (buildDepError "time-units"))
          (hsPkgs."transformers" or (buildDepError "transformers"))
          ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"));
        buildable = true;
        modules = [
          "Playground/Server"
          "Playground/Interpreter"
          "Playground/Usecases"
          "Crowdfunding"
          "CrowdfundingSimulations"
          "ErrorHandling"
          "ErrorHandlingSimulations"
          "Game"
          "GameSimulations"
          "SimulationUtils"
          "Starter"
          "StarterSimulations"
          "Vesting"
          "VestingSimulations"
          ];
        hsSourceDirs = [ "src" "usecases" ];
        };
      sublibs = {
        "plutus-playground-usecases" = {
          depends = [
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."insert-ordered-containers" or (buildDepError "insert-ordered-containers"))
            (hsPkgs."iots-export" or (buildDepError "iots-export"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."playground-common" or (buildDepError "playground-common"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."recursion-schemes" or (buildDepError "recursion-schemes"))
            (hsPkgs."row-types" or (buildDepError "row-types"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."time-units" or (buildDepError "time-units"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"));
          buildable = true;
          modules = [
            "Crowdfunding"
            "CrowdfundingSimulations"
            "ErrorHandling"
            "ErrorHandlingSimulations"
            "Game"
            "GameSimulations"
            "SimulationUtils"
            "Starter"
            "StarterSimulations"
            "Vesting"
            "VestingSimulations"
            ];
          hsSourceDirs = [ "usecases" ];
          };
        };
      exes = {
        "plutus-playground-server" = {
          depends = [
            (hsPkgs."adjunctions" or (buildDepError "adjunctions"))
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."aeson-pretty" or (buildDepError "aeson-pretty"))
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."exceptions" or (buildDepError "exceptions"))
            (hsPkgs."data-default-class" or (buildDepError "data-default-class"))
            (hsPkgs."filepath" or (buildDepError "filepath"))
            (hsPkgs."http-types" or (buildDepError "http-types"))
            (hsPkgs."iots-export" or (buildDepError "iots-export"))
            (hsPkgs."playground-common" or (buildDepError "playground-common"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."monad-logger" or (buildDepError "monad-logger"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."optparse-applicative" or (buildDepError "optparse-applicative"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."plutus-playground-server" or (buildDepError "plutus-playground-server"))
            (hsPkgs."plutus-playground-usecases" or (buildDepError "plutus-playground-usecases"))
            (hsPkgs."prometheus" or (buildDepError "prometheus"))
            (hsPkgs."purescript-bridge" or (buildDepError "purescript-bridge"))
            (hsPkgs."servant" or (buildDepError "servant"))
            (hsPkgs."servant-foreign" or (buildDepError "servant-foreign"))
            (hsPkgs."servant-purescript" or (buildDepError "servant-purescript"))
            (hsPkgs."servant-server" or (buildDepError "servant-server"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."time-units" or (buildDepError "time-units"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            (hsPkgs."wai" or (buildDepError "wai"))
            (hsPkgs."wai-cors" or (buildDepError "wai-cors"))
            (hsPkgs."wai-extra" or (buildDepError "wai-extra"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."recursion-schemes" or (buildDepError "recursion-schemes"))
            (hsPkgs."row-types" or (buildDepError "row-types"))
            (hsPkgs."warp" or (buildDepError "warp"))
            (hsPkgs."yaml" or (buildDepError "yaml"))
            ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"));
          buildable = true;
          modules = [
            "Webserver"
            "Types"
            "PSGenerator"
            "Crowdfunding"
            "CrowdfundingSimulations"
            "ErrorHandling"
            "ErrorHandlingSimulations"
            "Game"
            "GameSimulations"
            "SimulationUtils"
            "Starter"
            "StarterSimulations"
            "Vesting"
            "VestingSimulations"
            ];
          hsSourceDirs = [ "app" "usecases" ];
          mainPath = [
            "Main.hs"
            ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) "";
          };
        };
      tests = {
        "plutus-playground-server-test" = {
          depends = [
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."tasty-golden" or (buildDepError "tasty-golden"))
            (hsPkgs."insert-ordered-containers" or (buildDepError "insert-ordered-containers"))
            (hsPkgs."playground-common" or (buildDepError "playground-common"))
            (hsPkgs."iots-export" or (buildDepError "iots-export"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."plutus-playground-server" or (buildDepError "plutus-playground-server"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."plutus-playground-usecases" or (buildDepError "plutus-playground-usecases"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."time-units" or (buildDepError "time-units"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"));
          buildable = true;
          modules = [
            "GistSpec"
            "Paths_plutus_playground_server"
            "Playground/InterpreterSpec"
            "Playground/UsecasesSpec"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-playground-server;
    }