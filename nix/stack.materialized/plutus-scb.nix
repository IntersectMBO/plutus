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
      identifier = { name = "plutus-scb"; version = "0.1.0.0"; };
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
          (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
          (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"))
          (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
          (hsPkgs."playground-common" or (buildDepError "playground-common"))
          (hsPkgs."plutus-use-cases" or (buildDepError "plutus-use-cases"))
          (hsPkgs."iots-export" or (buildDepError "iots-export"))
          (hsPkgs."QuickCheck" or (buildDepError "QuickCheck"))
          (hsPkgs."aeson" or (buildDepError "aeson"))
          (hsPkgs."aeson-pretty" or (buildDepError "aeson-pretty"))
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."directory" or (buildDepError "directory"))
          (hsPkgs."errors" or (buildDepError "errors"))
          (hsPkgs."eventful-core" or (buildDepError "eventful-core"))
          (hsPkgs."eventful-memory" or (buildDepError "eventful-memory"))
          (hsPkgs."eventful-sql-common" or (buildDepError "eventful-sql-common"))
          (hsPkgs."eventful-sqlite" or (buildDepError "eventful-sqlite"))
          (hsPkgs."freer-simple" or (buildDepError "freer-simple"))
          (hsPkgs."generic-arbitrary" or (buildDepError "generic-arbitrary"))
          (hsPkgs."http-client" or (buildDepError "http-client"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."monad-logger" or (buildDepError "monad-logger"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."optparse-applicative" or (buildDepError "optparse-applicative"))
          (hsPkgs."persistent" or (buildDepError "persistent"))
          (hsPkgs."persistent-sqlite" or (buildDepError "persistent-sqlite"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          (hsPkgs."process" or (buildDepError "process"))
          (hsPkgs."quickcheck-instances" or (buildDepError "quickcheck-instances"))
          (hsPkgs."random" or (buildDepError "random"))
          (hsPkgs."row-types" or (buildDepError "row-types"))
          (hsPkgs."scientific" or (buildDepError "scientific"))
          (hsPkgs."servant" or (buildDepError "servant"))
          (hsPkgs."servant-client" or (buildDepError "servant-client"))
          (hsPkgs."servant-server" or (buildDepError "servant-server"))
          (hsPkgs."stm" or (buildDepError "stm"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."time-units" or (buildDepError "time-units"))
          (hsPkgs."transformers" or (buildDepError "transformers"))
          (hsPkgs."unliftio-core" or (buildDepError "unliftio-core"))
          (hsPkgs."unordered-containers" or (buildDepError "unordered-containers"))
          (hsPkgs."uuid" or (buildDepError "uuid"))
          (hsPkgs."vector" or (buildDepError "vector"))
          (hsPkgs."warp" or (buildDepError "warp"))
          (hsPkgs."yaml" or (buildDepError "yaml"))
          (hsPkgs."mwc-random" or (buildDepError "mwc-random"))
          (hsPkgs."primitive" or (buildDepError "primitive"))
          (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
          ];
        buildable = true;
        modules = [
          "Servant/Extra"
          "Cardano/ChainIndex/API"
          "Cardano/ChainIndex/Client"
          "Cardano/ChainIndex/Server"
          "Cardano/ChainIndex/Types"
          "Cardano/Node/API"
          "Cardano/Node/Client"
          "Cardano/Node/Follower"
          "Cardano/Node/Mock"
          "Cardano/Node/RandomTx"
          "Cardano/Node/Server"
          "Cardano/Node/Types"
          "Cardano/SigningProcess/API"
          "Cardano/SigningProcess/Server"
          "Cardano/SigningProcess/Client"
          "Cardano/Wallet/API"
          "Cardano/Wallet/Client"
          "Cardano/Wallet/Mock"
          "Cardano/Wallet/Server"
          "Cardano/Wallet/Types"
          "Control/Monad/Freer/Extra/Log"
          "Control/Monad/Freer/Extra/State"
          "Data/Time/Units/Extra"
          "Plutus/SCB/App"
          "Plutus/SCB/MockApp"
          "Plutus/SCB/Arbitrary"
          "Plutus/SCB/Command"
          "Plutus/SCB/ContractCLI"
          "Plutus/SCB/Core"
          "Plutus/SCB/Core/ContractInstance"
          "Plutus/SCB/Core/Projections"
          "Plutus/SCB/Effects/Contract"
          "Plutus/SCB/Effects/ContractTest"
          "Plutus/SCB/Effects/EventLog"
          "Plutus/SCB/Effects/MultiAgent"
          "Plutus/SCB/Effects/UUID"
          "Plutus/SCB/Webserver/Types"
          "Plutus/SCB/Webserver/API"
          "Plutus/SCB/Webserver/Server"
          "Plutus/SCB/Events"
          "Plutus/SCB/Events/Contract"
          "Plutus/SCB/Events/Node"
          "Plutus/SCB/Events/User"
          "Plutus/SCB/Events/Wallet"
          "Plutus/SCB/Query"
          "Plutus/SCB/Relation"
          "Plutus/SCB/Types"
          "Plutus/SCB/Utils"
          ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "plutus-scb" = {
          depends = [
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."aeson-pretty" or (buildDepError "aeson-pretty"))
            (hsPkgs."async" or (buildDepError "async"))
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."ekg" or (buildDepError "ekg"))
            (hsPkgs."filepath" or (buildDepError "filepath"))
            (hsPkgs."freer-simple" or (buildDepError "freer-simple"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."monad-logger" or (buildDepError "monad-logger"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."optparse-applicative" or (buildDepError "optparse-applicative"))
            (hsPkgs."playground-common" or (buildDepError "playground-common"))
            (hsPkgs."plutus-scb" or (buildDepError "plutus-scb"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-use-cases" or (buildDepError "plutus-use-cases"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."purescript-bridge" or (buildDepError "purescript-bridge"))
            (hsPkgs."row-types" or (buildDepError "row-types"))
            (hsPkgs."servant-purescript" or (buildDepError "servant-purescript"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."unliftio-core" or (buildDepError "unliftio-core"))
            (hsPkgs."uuid" or (buildDepError "uuid"))
            (hsPkgs."yaml" or (buildDepError "yaml"))
            (hsPkgs."containers" or (buildDepError "containers"))
            ];
          buildable = true;
          modules = [ "PSGenerator" ];
          hsSourceDirs = [ "app" ];
          mainPath = [ "Main.hs" ];
          };
        "plutus-contract" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."plutus-scb" or (buildDepError "plutus-scb"))
            (hsPkgs."plutus-use-cases" or (buildDepError "plutus-use-cases"))
            ];
          buildable = true;
          hsSourceDirs = [ "contract" ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "plutus-scb-test" = {
          depends = [
            (hsPkgs."QuickCheck" or (buildDepError "QuickCheck"))
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."aeson-pretty" or (buildDepError "aeson-pretty"))
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."eventful-core" or (buildDepError "eventful-core"))
            (hsPkgs."eventful-memory" or (buildDepError "eventful-memory"))
            (hsPkgs."freer-simple" or (buildDepError "freer-simple"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."monad-logger" or (buildDepError "monad-logger"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-scb" or (buildDepError "plutus-scb"))
            (hsPkgs."plutus-use-cases" or (buildDepError "plutus-use-cases"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."quickcheck-instances" or (buildDepError "quickcheck-instances"))
            (hsPkgs."servant-client" or (buildDepError "servant-client"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."tasty-quickcheck" or (buildDepError "tasty-quickcheck"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."row-types" or (buildDepError "row-types"))
            ];
          buildable = true;
          modules = [ "Plutus/SCB/CoreSpec" "Plutus/SCB/RelationSpec" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-scb;
    }