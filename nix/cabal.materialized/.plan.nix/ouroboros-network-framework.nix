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
      specVersion = "1.10";
      identifier = {
        name = "ouroboros-network-framework";
        version = "0.1.0.0";
        };
      license = "Apache-2.0";
      copyright = "2019 Input Output (Hong Kong) Ltd.";
      maintainer = "alex@well-typed.com, duncan@well-typed.com, marcin.szamotulski@iohk.io";
      author = "Alexander Vieth, Duncan Coutts, Marcin Szamotulski";
      homepage = "";
      url = "";
      synopsis = "";
      description = "";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [ "CHANGELOG.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."async" or (errorHandler.buildDepError "async"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
          (hsPkgs."io-sim-classes" or (errorHandler.buildDepError "io-sim-classes"))
          (hsPkgs."typed-protocols" or (errorHandler.buildDepError "typed-protocols"))
          (hsPkgs."network" or (errorHandler.buildDepError "network"))
          (hsPkgs."network-mux" or (errorHandler.buildDepError "network-mux"))
          (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
          (hsPkgs."Win32-network" or (errorHandler.buildDepError "Win32-network"))
          (hsPkgs."dns" or (errorHandler.buildDepError "dns"))
          (hsPkgs."iproute" or (errorHandler.buildDepError "iproute"))
          (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
          (hsPkgs."typed-protocols-examples" or (errorHandler.buildDepError "typed-protocols-examples"))
          (hsPkgs."cardano-prelude" or (errorHandler.buildDepError "cardano-prelude"))
          ] ++ (pkgs.lib).optionals (system.isWindows) [
          (hsPkgs."Win32-network" or (errorHandler.buildDepError "Win32-network"))
          (hsPkgs."Win32" or (errorHandler.buildDepError "Win32"))
          ];
        buildable = true;
        modules = [
          "Ouroboros/Network/Codec"
          "Ouroboros/Network/CodecCBORTerm"
          "Ouroboros/Network/Channel"
          "Ouroboros/Network/Driver"
          "Ouroboros/Network/Driver/Simple"
          "Ouroboros/Network/Driver/Limits"
          "Ouroboros/Network/ErrorPolicy"
          "Ouroboros/Network/IOManager"
          "Ouroboros/Network/Mux"
          "Ouroboros/Network/Protocol/Handshake/Type"
          "Ouroboros/Network/Protocol/Handshake/Codec"
          "Ouroboros/Network/Protocol/Handshake/Version"
          "Ouroboros/Network/Protocol/Handshake/Unversioned"
          "Ouroboros/Network/Protocol/Limits"
          "Ouroboros/Network/Server/ConnectionTable"
          "Ouroboros/Network/Server/Socket"
          "Ouroboros/Network/Server/RateLimiting"
          "Ouroboros/Network/Snocket"
          "Ouroboros/Network/Socket"
          "Ouroboros/Network/Subscription"
          "Ouroboros/Network/Subscription/Client"
          "Ouroboros/Network/Subscription/Dns"
          "Ouroboros/Network/Subscription/Ip"
          "Ouroboros/Network/Subscription/PeerState"
          "Ouroboros/Network/Subscription/Subscriber"
          "Ouroboros/Network/Subscription/Worker"
          ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "demo-ping-pong" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."network-mux" or (errorHandler.buildDepError "network-mux"))
            (hsPkgs."network" or (errorHandler.buildDepError "network"))
            (hsPkgs."ouroboros-network-framework" or (errorHandler.buildDepError "ouroboros-network-framework"))
            (hsPkgs."io-sim-classes" or (errorHandler.buildDepError "io-sim-classes"))
            (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."typed-protocols" or (errorHandler.buildDepError "typed-protocols"))
            (hsPkgs."typed-protocols-examples" or (errorHandler.buildDepError "typed-protocols-examples"))
            ] ++ (pkgs.lib).optionals (system.isWindows) [
            (hsPkgs."Win32-network" or (errorHandler.buildDepError "Win32-network"))
            (hsPkgs."Win32" or (errorHandler.buildDepError "Win32"))
            ];
          buildable = true;
          modules = [ "Network/TypedProtocol/PingPong/Codec/CBOR" ];
          hsSourceDirs = [ "demo" "test" ];
          mainPath = [
            "ping-pong.hs"
            ] ++ (pkgs.lib).optional (system.isWindows) "";
          };
        };
      tests = {
        "ouroboros-network-framework-tests" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."cborg" or (errorHandler.buildDepError "cborg"))
            (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
            (hsPkgs."io-sim-classes" or (errorHandler.buildDepError "io-sim-classes"))
            (hsPkgs."typed-protocols" or (errorHandler.buildDepError "typed-protocols"))
            (hsPkgs."typed-protocols-examples" or (errorHandler.buildDepError "typed-protocols-examples"))
            (hsPkgs."network" or (errorHandler.buildDepError "network"))
            (hsPkgs."network-mux" or (errorHandler.buildDepError "network-mux"))
            (hsPkgs."ouroboros-network-framework" or (errorHandler.buildDepError "ouroboros-network-framework"))
            (hsPkgs."ouroboros-network-testing" or (errorHandler.buildDepError "ouroboros-network-testing"))
            (hsPkgs."contra-tracer" or (errorHandler.buildDepError "contra-tracer"))
            (hsPkgs."dns" or (errorHandler.buildDepError "dns"))
            (hsPkgs."iproute" or (errorHandler.buildDepError "iproute"))
            (hsPkgs."io-sim" or (errorHandler.buildDepError "io-sim"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            ] ++ (pkgs.lib).optionals (system.isWindows) [
            (hsPkgs."Win32-network" or (errorHandler.buildDepError "Win32-network"))
            (hsPkgs."Win32" or (errorHandler.buildDepError "Win32"))
            ];
          buildable = true;
          modules = [
            "Network/TypedProtocol/PingPong/Codec/CBOR"
            "Network/TypedProtocol/ReqResp/Codec/CBOR"
            "Test/Network/TypedProtocol/PingPong/Codec"
            "Test/Network/TypedProtocol/ReqResp/Codec"
            "Test/Ouroboros/Network/Driver"
            "Test/Ouroboros/Network/Socket"
            "Test/Ouroboros/Network/Subscription"
            "Test/Ouroboros/Network/RateLimiting"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/12; }