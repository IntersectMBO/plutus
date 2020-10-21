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
          (hsPkgs."plutus-ledger" or (errorHandler.buildDepError "plutus-ledger"))
          (hsPkgs."plutus-tx" or (errorHandler.buildDepError "plutus-tx"))
          (hsPkgs."plutus-tx-plugin" or (errorHandler.buildDepError "plutus-tx-plugin"))
          (hsPkgs."plutus-contract" or (errorHandler.buildDepError "plutus-contract"))
          (hsPkgs."playground-common" or (errorHandler.buildDepError "playground-common"))
          (hsPkgs."plutus-use-cases" or (errorHandler.buildDepError "plutus-use-cases"))
          (hsPkgs."iots-export" or (errorHandler.buildDepError "iots-export"))
          (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."aeson-pretty" or (errorHandler.buildDepError "aeson-pretty"))
          (hsPkgs."async" or (errorHandler.buildDepError "async"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
          (hsPkgs."cardano-slotting" or (errorHandler.buildDepError "cardano-slotting"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
          (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
          (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
          (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
          (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
          (hsPkgs."eventful-core" or (errorHandler.buildDepError "eventful-core"))
          (hsPkgs."eventful-memory" or (errorHandler.buildDepError "eventful-memory"))
          (hsPkgs."eventful-sql-common" or (errorHandler.buildDepError "eventful-sql-common"))
          (hsPkgs."eventful-sqlite" or (errorHandler.buildDepError "eventful-sqlite"))
          (hsPkgs."freer-simple" or (errorHandler.buildDepError "freer-simple"))
          (hsPkgs."generic-arbitrary" or (errorHandler.buildDepError "generic-arbitrary"))
          (hsPkgs."http-client" or (errorHandler.buildDepError "http-client"))
          (hsPkgs."http-client-tls" or (errorHandler.buildDepError "http-client-tls"))
          (hsPkgs."http-types" or (errorHandler.buildDepError "http-types"))
          (hsPkgs."io-sim-classes" or (errorHandler.buildDepError "io-sim-classes"))
          (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
          (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
          (hsPkgs."monad-logger" or (errorHandler.buildDepError "monad-logger"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."network" or (errorHandler.buildDepError "network"))
          (hsPkgs."network-mux" or (errorHandler.buildDepError "network-mux"))
          (hsPkgs."newtype-generics" or (errorHandler.buildDepError "newtype-generics"))
          (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
          (hsPkgs."ouroboros-network" or (errorHandler.buildDepError "ouroboros-network"))
          (hsPkgs."ouroboros-network-framework" or (errorHandler.buildDepError "ouroboros-network-framework"))
          (hsPkgs."persistent" or (errorHandler.buildDepError "persistent"))
          (hsPkgs."persistent-sqlite" or (errorHandler.buildDepError "persistent-sqlite"))
          (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
          (hsPkgs."process" or (errorHandler.buildDepError "process"))
          (hsPkgs."quickcheck-instances" or (errorHandler.buildDepError "quickcheck-instances"))
          (hsPkgs."random" or (errorHandler.buildDepError "random"))
          (hsPkgs."row-types" or (errorHandler.buildDepError "row-types"))
          (hsPkgs."scientific" or (errorHandler.buildDepError "scientific"))
          (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
          (hsPkgs."servant" or (errorHandler.buildDepError "servant"))
          (hsPkgs."servant-client" or (errorHandler.buildDepError "servant-client"))
          (hsPkgs."servant-server" or (errorHandler.buildDepError "servant-server"))
          (hsPkgs."servant-swagger" or (errorHandler.buildDepError "servant-swagger"))
          (hsPkgs."swagger2" or (errorHandler.buildDepError "swagger2"))
          (hsPkgs."typed-protocols" or (errorHandler.buildDepError "typed-protocols"))
          (hsPkgs."typed-protocols-examples" or (errorHandler.buildDepError "typed-protocols-examples"))
          (hsPkgs."servant-websockets" or (errorHandler.buildDepError "servant-websockets"))
          (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."time-units" or (errorHandler.buildDepError "time-units"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          (hsPkgs."unliftio-core" or (errorHandler.buildDepError "unliftio-core"))
          (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
          (hsPkgs."uuid" or (errorHandler.buildDepError "uuid"))
          (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
          (hsPkgs."warp" or (errorHandler.buildDepError "warp"))
          (hsPkgs."Win32-network" or (errorHandler.buildDepError "Win32-network"))
          (hsPkgs."websockets" or (errorHandler.buildDepError "websockets"))
          (hsPkgs."yaml" or (errorHandler.buildDepError "yaml"))
          (hsPkgs."mwc-random" or (errorHandler.buildDepError "mwc-random"))
          (hsPkgs."primitive" or (errorHandler.buildDepError "primitive"))
          (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
          (hsPkgs."iohk-monitoring" or (errorHandler.buildDepError "iohk-monitoring"))
          (hsPkgs."lobemo-backend-ekg" or (errorHandler.buildDepError "lobemo-backend-ekg"))
          (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
          ];
        buildable = true;
        modules = [
          "Servant/Extra"
          "Cardano/BM/Data/Tracer/Extras"
          "Cardano/ChainIndex/API"
          "Cardano/ChainIndex/Client"
          "Cardano/ChainIndex/Server"
          "Cardano/ChainIndex/Types"
          "Cardano/Metadata/API"
          "Cardano/Metadata/Client"
          "Cardano/Metadata/Server"
          "Cardano/Metadata/Types"
          "Cardano/Node/API"
          "Cardano/Node/Client"
          "Cardano/Node/Follower"
          "Cardano/Node/Mock"
          "Cardano/Node/RandomTx"
          "Cardano/Node/Server"
          "Cardano/Node/Types"
          "Cardano/Protocol/ChainEffect"
          "Cardano/Protocol/FollowerEffect"
          "Cardano/Protocol/Socket/Type"
          "Cardano/Protocol/Socket/Server"
          "Cardano/Protocol/Socket/Client"
          "Cardano/SigningProcess/API"
          "Cardano/SigningProcess/Server"
          "Cardano/SigningProcess/Client"
          "Cardano/Wallet/API"
          "Cardano/Wallet/Client"
          "Cardano/Wallet/Mock"
          "Cardano/Wallet/Server"
          "Cardano/Wallet/Types"
          "Control/Monad/Freer/Delay"
          "Control/Monad/Freer/Extra/Log"
          "Control/Monad/Freer/Extra/State"
          "Control/Monad/Freer/WebSocket"
          "Control/Concurrent/Availability"
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
          "Plutus/SCB/Effects/ContractRuntime"
          "Plutus/SCB/Effects/ContractTest/AtomicSwap"
          "Plutus/SCB/Effects/ContractTest/PayToWallet"
          "Plutus/SCB/Effects/EventLog"
          "Plutus/SCB/Effects/MultiAgent"
          "Plutus/SCB/Effects/UUID"
          "Plutus/SCB/Instances"
          "Plutus/SCB/MonadLoggerBridge"
          "Plutus/SCB/Monitoring"
          "Plutus/SCB/Swagger"
          "Plutus/SCB/Webserver/API"
          "Plutus/SCB/Webserver/Handler"
          "Plutus/SCB/Webserver/Server"
          "Plutus/SCB/Webserver/Types"
          "Plutus/SCB/Webserver/WebSocket"
          "Plutus/SCB/Events"
          "Plutus/SCB/Events/Contract"
          "Plutus/SCB/Events/Node"
          "Plutus/SCB/Events/User"
          "Plutus/SCB/Events/Wallet"
          "Plutus/SCB/ParseStringifiedJSON"
          "Plutus/SCB/Query"
          "Plutus/SCB/Relation"
          "Plutus/SCB/SCBLogMsg"
          "Plutus/SCB/Types"
          "Plutus/SCB/Utils"
          ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "plutus-scb" = {
          depends = [
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."aeson-pretty" or (errorHandler.buildDepError "aeson-pretty"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."freer-simple" or (errorHandler.buildDepError "freer-simple"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."monad-logger" or (errorHandler.buildDepError "monad-logger"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."playground-common" or (errorHandler.buildDepError "playground-common"))
            (hsPkgs."plutus-scb" or (errorHandler.buildDepError "plutus-scb"))
            (hsPkgs."plutus-ledger" or (errorHandler.buildDepError "plutus-ledger"))
            (hsPkgs."plutus-contract" or (errorHandler.buildDepError "plutus-contract"))
            (hsPkgs."plutus-use-cases" or (errorHandler.buildDepError "plutus-use-cases"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."purescript-bridge" or (errorHandler.buildDepError "purescript-bridge"))
            (hsPkgs."row-types" or (errorHandler.buildDepError "row-types"))
            (hsPkgs."servant-purescript" or (errorHandler.buildDepError "servant-purescript"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."unliftio-core" or (errorHandler.buildDepError "unliftio-core"))
            (hsPkgs."uuid" or (errorHandler.buildDepError "uuid"))
            (hsPkgs."yaml" or (errorHandler.buildDepError "yaml"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."iohk-monitoring" or (errorHandler.buildDepError "iohk-monitoring"))
            (hsPkgs."time-units" or (errorHandler.buildDepError "time-units"))
            (hsPkgs."servant-client" or (errorHandler.buildDepError "servant-client"))
            (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
            (hsPkgs."lobemo-backend-ekg" or (errorHandler.buildDepError "lobemo-backend-ekg"))
            ];
          buildable = true;
          modules = [ "PSGenerator" ];
          hsSourceDirs = [ "app" ];
          mainPath = [ "Main.hs" ];
          };
        "plutus-game" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-scb" or (errorHandler.buildDepError "plutus-scb"))
            (hsPkgs."plutus-use-cases" or (errorHandler.buildDepError "plutus-use-cases"))
            ];
          buildable = true;
          hsSourceDirs = [ "game-contract" ];
          mainPath = [ "Main.hs" ];
          };
        "plutus-currency" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-scb" or (errorHandler.buildDepError "plutus-scb"))
            (hsPkgs."plutus-use-cases" or (errorHandler.buildDepError "plutus-use-cases"))
            ];
          buildable = true;
          hsSourceDirs = [ "currency-contract" ];
          mainPath = [ "Main.hs" ];
          };
        "plutus-atomic-swap" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-scb" or (errorHandler.buildDepError "plutus-scb"))
            ];
          buildable = true;
          hsSourceDirs = [ "atomic-swap-contract" ];
          mainPath = [ "Main.hs" ];
          };
        "plutus-pay-to-wallet" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-scb" or (errorHandler.buildDepError "plutus-scb"))
            ];
          buildable = true;
          hsSourceDirs = [ "pay-to-wallet-contract" ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "plutus-scb-test" = {
          depends = [
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."aeson-pretty" or (errorHandler.buildDepError "aeson-pretty"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."eventful-core" or (errorHandler.buildDepError "eventful-core"))
            (hsPkgs."eventful-memory" or (errorHandler.buildDepError "eventful-memory"))
            (hsPkgs."freer-simple" or (errorHandler.buildDepError "freer-simple"))
            (hsPkgs."http-client" or (errorHandler.buildDepError "http-client"))
            (hsPkgs."http-client-tls" or (errorHandler.buildDepError "http-client-tls"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."monad-logger" or (errorHandler.buildDepError "monad-logger"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."plutus-contract" or (errorHandler.buildDepError "plutus-contract"))
            (hsPkgs."plutus-scb" or (errorHandler.buildDepError "plutus-scb"))
            (hsPkgs."plutus-use-cases" or (errorHandler.buildDepError "plutus-use-cases"))
            (hsPkgs."plutus-ledger" or (errorHandler.buildDepError "plutus-ledger"))
            (hsPkgs."quickcheck-instances" or (errorHandler.buildDepError "quickcheck-instances"))
            (hsPkgs."servant-client" or (errorHandler.buildDepError "servant-client"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."smallcheck" or (errorHandler.buildDepError "smallcheck"))
            (hsPkgs."tasty-smallcheck" or (errorHandler.buildDepError "tasty-smallcheck"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."row-types" or (errorHandler.buildDepError "row-types"))
            ];
          buildable = true;
          modules = [
            "Plutus/SCB/CoreSpec"
            "Plutus/SCB/RelationSpec"
            "Plutus/SCB/Events/ContractSpec"
            "Cardano/Metadata/ServerSpec"
            "Cardano/Metadata/TypesSpec"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-scb;
    }