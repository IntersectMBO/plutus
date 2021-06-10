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
    flags = { asserts = false; ipv6 = false; cddl = true; };
    package = {
      specVersion = "1.10";
      identifier = { name = "ouroboros-network"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "2019 Input Output (Hong Kong) Ltd.";
      maintainer = "";
      author = "Alexander Vieth, Marcin Szamotulski, Duncan Coutts";
      homepage = "";
      url = "";
      synopsis = "A networking layer for the Ouroboros blockchain protocol";
      description = "";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = ".";
      dataFiles = [
        "test-cddl/specs/handshake-node-to-node.cddl"
        "test-cddl/specs/handshake-node-to-client.cddl"
        "test-cddl/specs/chain-sync.cddl"
        "test-cddl/specs/block-fetch.cddl"
        "test-cddl/specs/tx-submission.cddl"
        "test-cddl/specs/tx-submission2.cddl"
        "test-cddl/specs/keep-alive.cddl"
        "test-cddl/specs/local-tx-submission.cddl"
        "test-cddl/specs/local-state-query.cddl"
        ];
      extraSrcFiles = [ "ChangeLog.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."async" or (errorHandler.buildDepError "async"))
          (hsPkgs."base16-bytestring" or (errorHandler.buildDepError "base16-bytestring"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
          (hsPkgs."dns" or (errorHandler.buildDepError "dns"))
          (hsPkgs."fingertree" or (errorHandler.buildDepError "fingertree"))
          (hsPkgs."iproute" or (errorHandler.buildDepError "iproute"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."nothunks" or (errorHandler.buildDepError "nothunks"))
          (hsPkgs."network" or (errorHandler.buildDepError "network"))
          (hsPkgs."psqueues" or (errorHandler.buildDepError "psqueues"))
          (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
          (hsPkgs."random" or (errorHandler.buildDepError "random"))
          (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
          (hsPkgs."strict-containers" or (errorHandler.buildDepError "strict-containers"))
          (hsPkgs."cardano-binary" or (errorHandler.buildDepError "cardano-binary"))
          (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
          (hsPkgs."cardano-slotting" or (errorHandler.buildDepError "cardano-slotting"))
          (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
          (hsPkgs."io-sim-classes" or (errorHandler.buildDepError "io-sim-classes"))
          (hsPkgs."network-mux" or (errorHandler.buildDepError "network-mux"))
          (hsPkgs."ouroboros-network-framework" or (errorHandler.buildDepError "ouroboros-network-framework"))
          (hsPkgs."typed-protocols" or (errorHandler.buildDepError "typed-protocols"))
          (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          ];
        buildable = true;
        modules = [
          "Ouroboros/Network/PeerSelection/Governor/ActivePeers"
          "Ouroboros/Network/PeerSelection/Governor/EstablishedPeers"
          "Ouroboros/Network/PeerSelection/Governor/KnownPeers"
          "Ouroboros/Network/PeerSelection/Governor/Monitor"
          "Ouroboros/Network/PeerSelection/Governor/RootPeers"
          "Ouroboros/Network/PeerSelection/Governor/Types"
          "Ouroboros/Network/AnchoredFragment"
          "Ouroboros/Network/AnchoredSeq"
          "Ouroboros/Network/Block"
          "Ouroboros/Network/BlockFetch"
          "Ouroboros/Network/BlockFetch/Client"
          "Ouroboros/Network/BlockFetch/ClientRegistry"
          "Ouroboros/Network/BlockFetch/ClientState"
          "Ouroboros/Network/BlockFetch/Decision"
          "Ouroboros/Network/BlockFetch/DeltaQ"
          "Ouroboros/Network/BlockFetch/State"
          "Ouroboros/Network/Counter"
          "Ouroboros/Network/DeltaQ"
          "Ouroboros/Network/Diffusion"
          "Ouroboros/Network/KeepAlive"
          "Ouroboros/Network/Magic"
          "Ouroboros/Network/NodeToNode"
          "Ouroboros/Network/NodeToNode/Version"
          "Ouroboros/Network/NodeToClient"
          "Ouroboros/Network/NodeToClient/Version"
          "Ouroboros/Network/Tracers"
          "Ouroboros/Network/Point"
          "Ouroboros/Network/PeerSelection/Types"
          "Ouroboros/Network/PeerSelection/EstablishedPeers"
          "Ouroboros/Network/PeerSelection/KnownPeers"
          "Ouroboros/Network/PeerSelection/LedgerPeers"
          "Ouroboros/Network/PeerSelection/LocalRootPeers"
          "Ouroboros/Network/PeerSelection/RootPeersDNS"
          "Ouroboros/Network/PeerSelection/Governor"
          "Ouroboros/Network/Protocol/ChainSync/Client"
          "Ouroboros/Network/Protocol/ChainSync/ClientPipelined"
          "Ouroboros/Network/Protocol/ChainSync/Codec"
          "Ouroboros/Network/Protocol/ChainSync/Server"
          "Ouroboros/Network/Protocol/ChainSync/Type"
          "Ouroboros/Network/Protocol/ChainSync/PipelineDecision"
          "Ouroboros/Network/Protocol/ChainSync/Examples"
          "Ouroboros/Network/Protocol/BlockFetch/Type"
          "Ouroboros/Network/Protocol/BlockFetch/Client"
          "Ouroboros/Network/Protocol/BlockFetch/Server"
          "Ouroboros/Network/Protocol/BlockFetch/Codec"
          "Ouroboros/Network/Protocol/LocalStateQuery/Client"
          "Ouroboros/Network/Protocol/LocalStateQuery/Codec"
          "Ouroboros/Network/Protocol/LocalStateQuery/Examples"
          "Ouroboros/Network/Protocol/LocalStateQuery/Server"
          "Ouroboros/Network/Protocol/LocalStateQuery/Type"
          "Ouroboros/Network/Protocol/LocalTxMonitor/Type"
          "Ouroboros/Network/Protocol/TipSample/Type"
          "Ouroboros/Network/Protocol/TipSample/Client"
          "Ouroboros/Network/Protocol/TipSample/Server"
          "Ouroboros/Network/Protocol/TipSample/Codec"
          "Ouroboros/Network/Protocol/TxSubmission/Type"
          "Ouroboros/Network/Protocol/TxSubmission/Client"
          "Ouroboros/Network/Protocol/TxSubmission/Server"
          "Ouroboros/Network/Protocol/TxSubmission/Codec"
          "Ouroboros/Network/Protocol/TxSubmission2/Type"
          "Ouroboros/Network/Protocol/TxSubmission2/Codec"
          "Ouroboros/Network/Protocol/LocalTxSubmission/Type"
          "Ouroboros/Network/Protocol/LocalTxSubmission/Client"
          "Ouroboros/Network/Protocol/LocalTxSubmission/Server"
          "Ouroboros/Network/Protocol/LocalTxSubmission/Codec"
          "Ouroboros/Network/Protocol/KeepAlive/Type"
          "Ouroboros/Network/Protocol/KeepAlive/Client"
          "Ouroboros/Network/Protocol/KeepAlive/Server"
          "Ouroboros/Network/Protocol/KeepAlive/Codec"
          "Ouroboros/Network/Protocol/Trans/Hello/Type"
          "Ouroboros/Network/Protocol/Trans/Hello/Codec"
          "Ouroboros/Network/Protocol/Trans/Hello/Util"
          "Ouroboros/Network/TxSubmission/Inbound"
          "Ouroboros/Network/TxSubmission/Mempool/Reader"
          "Ouroboros/Network/TxSubmission/Outbound"
          "Ouroboros/Network/MockChain/Chain"
          "Ouroboros/Network/MockChain/ProducerState"
          "Ouroboros/Network/Testing/ConcreteBlock"
          ];
        hsSourceDirs = [ "src" ];
        };
      sublibs = {
        "ouroboros-protocol-tests" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."pipes" or (errorHandler.buildDepError "pipes"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
            (hsPkgs."strict-containers" or (errorHandler.buildDepError "strict-containers"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
            (hsPkgs."cardano-slotting" or (errorHandler.buildDepError "cardano-slotting"))
            (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
            (hsPkgs."io-sim" or (errorHandler.buildDepError "io-sim"))
            (hsPkgs."io-sim-classes" or (errorHandler.buildDepError "io-sim-classes"))
            (hsPkgs."ouroboros-network" or (errorHandler.buildDepError "ouroboros-network"))
            (hsPkgs."ouroboros-network-framework" or (errorHandler.buildDepError "ouroboros-network-framework"))
            (hsPkgs."ouroboros-network-testing" or (errorHandler.buildDepError "ouroboros-network-testing"))
            (hsPkgs."typed-protocols" or (errorHandler.buildDepError "typed-protocols"))
            ];
          buildable = true;
          modules = [
            "Ouroboros/Network/Protocol/BlockFetch/Direct"
            "Ouroboros/Network/Protocol/BlockFetch/Examples"
            "Ouroboros/Network/Protocol/BlockFetch/Test"
            "Ouroboros/Network/Protocol/ChainSync/Direct"
            "Ouroboros/Network/Protocol/ChainSync/DirectPipelined"
            "Ouroboros/Network/Protocol/ChainSync/ExamplesPipelined"
            "Ouroboros/Network/Protocol/ChainSync/Test"
            "Ouroboros/Network/Protocol/Handshake/Direct"
            "Ouroboros/Network/Protocol/Handshake/Test"
            "Ouroboros/Network/Protocol/LocalStateQuery/Direct"
            "Ouroboros/Network/Protocol/LocalStateQuery/Test"
            "Ouroboros/Network/Protocol/LocalTxSubmission/Direct"
            "Ouroboros/Network/Protocol/LocalTxSubmission/Examples"
            "Ouroboros/Network/Protocol/LocalTxSubmission/Test"
            "Ouroboros/Network/Protocol/TipSample/Direct"
            "Ouroboros/Network/Protocol/TipSample/Examples"
            "Ouroboros/Network/Protocol/TipSample/Test"
            "Ouroboros/Network/Protocol/TxSubmission/Direct"
            "Ouroboros/Network/Protocol/TxSubmission/Examples"
            "Ouroboros/Network/Protocol/TxSubmission/Test"
            "Ouroboros/Network/Protocol/TxSubmission2/Test"
            "Ouroboros/Network/Protocol/KeepAlive/Direct"
            "Ouroboros/Network/Protocol/KeepAlive/Examples"
            "Ouroboros/Network/Protocol/KeepAlive/Test"
            "Test/ChainGenerators"
            "Test/ChainProducerState"
            "Test/Ouroboros/Network/Testing/Utils"
            ];
          hsSourceDirs = [ "protocol-tests" ];
          };
        };
      exes = {
        "demo-chain-sync" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."network" or (errorHandler.buildDepError "network"))
            (hsPkgs."random" or (errorHandler.buildDepError "random"))
            (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
            (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
            (hsPkgs."network-mux" or (errorHandler.buildDepError "network-mux"))
            (hsPkgs."typed-protocols" or (errorHandler.buildDepError "typed-protocols"))
            (hsPkgs."ouroboros-network-framework" or (errorHandler.buildDepError "ouroboros-network-framework"))
            (hsPkgs."ouroboros-network" or (errorHandler.buildDepError "ouroboros-network"))
            ];
          buildable = true;
          hsSourceDirs = [ "demo" ];
          mainPath = [ "chain-sync.hs" ];
          };
        };
      tests = {
        "test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."array" or (errorHandler.buildDepError "array"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."binary" or (errorHandler.buildDepError "binary"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."dns" or (errorHandler.buildDepError "dns"))
            (hsPkgs."fingertree" or (errorHandler.buildDepError "fingertree"))
            (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
            (hsPkgs."iproute" or (errorHandler.buildDepError "iproute"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."network" or (errorHandler.buildDepError "network"))
            (hsPkgs."pipes" or (errorHandler.buildDepError "pipes"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."psqueues" or (errorHandler.buildDepError "psqueues"))
            (hsPkgs."random" or (errorHandler.buildDepError "random"))
            (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
            (hsPkgs."splitmix" or (errorHandler.buildDepError "splitmix"))
            (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
            (hsPkgs."strict-containers" or (errorHandler.buildDepError "strict-containers"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."cardano-binary" or (errorHandler.buildDepError "cardano-binary"))
            (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
            (hsPkgs."cardano-slotting" or (errorHandler.buildDepError "cardano-slotting"))
            (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
            (hsPkgs."nothunks" or (errorHandler.buildDepError "nothunks"))
            (hsPkgs."io-sim" or (errorHandler.buildDepError "io-sim"))
            (hsPkgs."io-sim-classes" or (errorHandler.buildDepError "io-sim-classes"))
            (hsPkgs."network-mux" or (errorHandler.buildDepError "network-mux"))
            (hsPkgs."ouroboros-network" or (errorHandler.buildDepError "ouroboros-network"))
            (hsPkgs."ouroboros-network-framework" or (errorHandler.buildDepError "ouroboros-network-framework"))
            (hsPkgs."ouroboros-network-testing" or (errorHandler.buildDepError "ouroboros-network-testing"))
            (hsPkgs."ouroboros-network".components.sublibs.ouroboros-protocol-tests or (errorHandler.buildDepError "ouroboros-network:ouroboros-protocol-tests"))
            (hsPkgs."typed-protocols" or (errorHandler.buildDepError "typed-protocols"))
            ] ++ (pkgs.lib).optionals (system.isWindows) [
            (hsPkgs."Win32-network" or (errorHandler.buildDepError "Win32-network"))
            (hsPkgs."Win32" or (errorHandler.buildDepError "Win32"))
            ];
          buildable = true;
          modules = [
            "Ouroboros/Network/BlockFetch/Examples"
            "Ouroboros/Network/MockNode"
            "Test/AnchoredFragment"
            "Test/Chain"
            "Test/LedgerPeers"
            "Test/Ouroboros/Network/BlockFetch"
            "Test/Ouroboros/Network/KeepAlive"
            "Test/Ouroboros/Network/MockNode"
            "Test/Ouroboros/Network/TxSubmission"
            "Test/Ouroboros/Network/PeerSelection"
            "Test/Ouroboros/Network/PeerSelection/Instances"
            "Test/Ouroboros/Network/PeerSelection/LocalRootPeers"
            "Test/Ouroboros/Network/PeerSelection/MockEnvironment"
            "Test/Ouroboros/Network/PeerSelection/PeerGraph"
            "Test/Ouroboros/Network/PeerSelection/Script"
            "Test/Ouroboros/Network/NodeToNode/Version"
            "Test/Ouroboros/Network/NodeToClient/Version"
            "Test/Mux"
            "Test/Pipe"
            "Test/Socket"
            "Test/PeerState"
            "Test/Version"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Main.hs" ];
          };
        "cddl" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."fingertree" or (errorHandler.buildDepError "fingertree"))
            (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."pipes" or (errorHandler.buildDepError "pipes"))
            (hsPkgs."process-extras" or (errorHandler.buildDepError "process-extras"))
            (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."quickcheck-instances" or (errorHandler.buildDepError "quickcheck-instances"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."cardano-binary" or (errorHandler.buildDepError "cardano-binary"))
            (hsPkgs."cardano-slotting" or (errorHandler.buildDepError "cardano-slotting"))
            (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
            (hsPkgs."io-sim" or (errorHandler.buildDepError "io-sim"))
            (hsPkgs."io-sim-classes" or (errorHandler.buildDepError "io-sim-classes"))
            (hsPkgs."network-mux" or (errorHandler.buildDepError "network-mux"))
            (hsPkgs."typed-protocols" or (errorHandler.buildDepError "typed-protocols"))
            (hsPkgs."ouroboros-network-framework" or (errorHandler.buildDepError "ouroboros-network-framework"))
            (hsPkgs."ouroboros-network" or (errorHandler.buildDepError "ouroboros-network"))
            (hsPkgs."ouroboros-network".components.sublibs.ouroboros-protocol-tests or (errorHandler.buildDepError "ouroboros-network:ouroboros-protocol-tests"))
            ];
          buildable = if flags.cddl then true else false;
          hsSourceDirs = [ "test-cddl" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/15; }