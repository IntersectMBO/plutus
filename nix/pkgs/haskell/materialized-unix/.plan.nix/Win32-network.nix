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
    flags = { demo = false; };
    package = {
      specVersion = "2.4";
      identifier = { name = "Win32-network"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "2019 Input Output (Hong Kong) Ltd.";
      maintainer = "duncan@well-typed.com, marcin.szamotulski@iohk.io";
      author = "Duncan Coutts, Marcin Szamotulski";
      homepage = "";
      url = "";
      synopsis = "Win32 network API";
      description = "";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [ "include/Win32-network.h" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = (([
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          ] ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."network" or (errorHandler.buildDepError "network"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."Win32" or (errorHandler.buildDepError "Win32"));
        libs = (pkgs.lib).optional (system.isWindows) (pkgs."ws2_32" or (errorHandler.sysDepError "ws2_32"));
        buildable = true;
        modules = [
          "System/IOManager"
          ] ++ (pkgs.lib).optionals (system.isWindows) [
          "System/Win32/Async/IOData"
          "System/Win32/Async/IOManager"
          "System/Win32/Async/Overlapped"
          "System/Win32/Async/Socket/Syscalls"
          "System/Win32/Async/WSABuf"
          "System/Win32/NamedPipes"
          "System/Win32/Async"
          "System/Win32/Async/File"
          "System/Win32/Async/ErrCode"
          "System/Win32/Async/Socket"
          "System/Win32/Async/Socket/ByteString"
          "System/Win32/Async/Socket/ByteString/Lazy"
          "System/Win32/Async/Internal"
          ];
        hsSourceDirs = [ "src" ];
        includeDirs = (pkgs.lib).optional (system.isWindows) "include";
        };
      exes = {
        "named-pipe-demo" = {
          depends = (([
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."Win32-network" or (errorHandler.buildDepError "Win32-network"))
            ] ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."binary" or (errorHandler.buildDepError "binary"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."Win32" or (errorHandler.buildDepError "Win32"));
          buildable = true;
          hsSourceDirs = [ "demo" ];
          mainPath = (([
            "named-pipe-demo.hs"
            ] ++ (pkgs.lib).optional (system.isWindows) "") ++ (pkgs.lib).optional (system.isWindows) "") ++ (pkgs.lib).optional (system.isWindows) "";
          };
        };
      tests = {
        "test" = {
          depends = (((((((((([
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."Win32-network" or (errorHandler.buildDepError "Win32-network"))
            ] ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."async" or (errorHandler.buildDepError "async"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."binary" or (errorHandler.buildDepError "binary"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."network" or (errorHandler.buildDepError "network"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."stm" or (errorHandler.buildDepError "stm"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."quickcheck-instances" or (errorHandler.buildDepError "quickcheck-instances"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."Win32" or (errorHandler.buildDepError "Win32"));
          buildable = true;
          modules = (pkgs.lib).optionals (system.isWindows) [
            "Test/Generators"
            "Test/Async/PingPong"
            "Test/Async/Handle"
            "Test/Async/Socket"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/44; }