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
    flags = { devel = false; };
    package = {
      specVersion = "1.18";
      identifier = { name = "network"; version = "3.1.2.1"; };
      license = "BSD-3-Clause";
      copyright = "";
      maintainer = "Kazu Yamamoto, Evan Borden";
      author = "";
      homepage = "https://github.com/haskell/network";
      url = "";
      synopsis = "Low-level networking interface";
      description = "This package provides a low-level networking interface.\n\n=== High-Level Packages\nOther packages provide higher level interfaces:\n\n* connection\n* hookup\n* network-simple\n\n=== Extended Packages\n@network@ seeks to provide a cross-platform core for networking. As such some\nAPIs live in extended libraries. Packages in the @network@ ecosystem are\noften prefixed with @network-@.\n\n==== @network-bsd@\nIn @network-3.0.0.0@ the @Network.BSD@ module was split off into its own\npackage, @network-bsd-3.0.0.0@.\n\n==== @network-uri@\nIn @network-2.6@ the @Network.URI@ module was split off into its own package,\n@network-uri-2.6@. If you're using the @Network.URI@ module you can\nautomatically get it from the right package by adding this to your @.cabal@\nfile:\n\n> library\n>   build-depends: network-uri-flag";
      buildType = "Configure";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [
        "README.md"
        "CHANGELOG.md"
        "examples/*.hs"
        "tests/*.hs"
        "config.guess"
        "config.sub"
        "install-sh"
        "configure.ac"
        "configure"
        "include/HsNetworkConfig.h.in"
        "include/HsNet.h"
        "include/HsNetDef.h"
        "cbits/asyncAccept.c"
        "cbits/initWinSock.c"
        "cbits/winSockErr.c"
        "cbits/cmsg.c"
        ];
      extraTmpFiles = [
        "config.log"
        "config.status"
        "autom4te.cache"
        "network.buildinfo"
        "include/HsNetworkConfig.h"
        ];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
          (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
          ];
        libs = (pkgs.lib).optionals (system.isSolaris) [
          (pkgs."nsl" or (errorHandler.sysDepError "nsl"))
          (pkgs."socket" or (errorHandler.sysDepError "socket"))
          ] ++ (pkgs.lib).optionals (system.isWindows) [
          (pkgs."ws2_32" or (errorHandler.sysDepError "ws2_32"))
          (pkgs."iphlpapi" or (errorHandler.sysDepError "iphlpapi"))
          (pkgs."mswsock" or (errorHandler.sysDepError "mswsock"))
          ];
        build-tools = [
          (hsPkgs.buildPackages.hsc2hs.components.exes.hsc2hs or (pkgs.buildPackages.hsc2hs or (errorHandler.buildToolDepError "hsc2hs:hsc2hs")))
          ];
        buildable = true;
        modules = ([
          "Network/Socket/Buffer"
          "Network/Socket/ByteString/IO"
          "Network/Socket/ByteString/Internal"
          "Network/Socket/Cbits"
          "Network/Socket/Fcntl"
          "Network/Socket/Flag"
          "Network/Socket/Handle"
          "Network/Socket/If"
          "Network/Socket/Imports"
          "Network/Socket/Info"
          "Network/Socket/Name"
          "Network/Socket/Options"
          "Network/Socket/ReadShow"
          "Network/Socket/Shutdown"
          "Network/Socket/SockAddr"
          "Network/Socket/Syscall"
          "Network/Socket/Types"
          "Network/Socket/Unix"
          "Network/Socket"
          "Network/Socket/Address"
          "Network/Socket/ByteString"
          "Network/Socket/ByteString/Lazy"
          "Network/Socket/Internal"
          ] ++ (pkgs.lib).optionals (!system.isWindows) [
          "Network/Socket/ByteString/Lazy/Posix"
          "Network/Socket/Posix/Cmsg"
          "Network/Socket/Posix/CmsgHdr"
          "Network/Socket/Posix/IOVec"
          "Network/Socket/Posix/MsgHdr"
          ]) ++ (pkgs.lib).optionals (system.isWindows) [
          "Network/Socket/ByteString/Lazy/Windows"
          "Network/Socket/Win32/Cmsg"
          "Network/Socket/Win32/CmsgHdr"
          "Network/Socket/Win32/WSABuf"
          "Network/Socket/Win32/MsgHdr"
          ];
        cSources = [
          "cbits/HsNet.c"
          "cbits/cmsg.c"
          ] ++ (pkgs.lib).optionals (system.isWindows) [
          "cbits/initWinSock.c"
          "cbits/winSockErr.c"
          "cbits/asyncAccept.c"
          ];
        includeDirs = [ "include" ];
        includes = [ "HsNet.h" "HsNetDef.h" "alignment.h" "win32defs.h" ];
        };
      tests = {
        "spec" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."HUnit" or (errorHandler.buildDepError "HUnit"))
            (hsPkgs."network" or (errorHandler.buildDepError "network"))
            (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
            (hsPkgs."hspec" or (errorHandler.buildDepError "hspec"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.hspec-discover.components.exes.hspec-discover or (pkgs.buildPackages.hspec-discover or (errorHandler.buildToolDepError "hspec-discover:hspec-discover")))
            ];
          buildable = true;
          modules = [
            "Network/Test/Common"
            "Network/SocketSpec"
            "Network/Socket/ByteStringSpec"
            "Network/Socket/ByteString/LazySpec"
            ];
          hsSourceDirs = [ "tests" ];
          mainPath = [ "Spec.hs" ];
          };
        "doctests" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."doctest" or (errorHandler.buildDepError "doctest"))
            (hsPkgs."network" or (errorHandler.buildDepError "network"))
            ];
          buildable = false;
          hsSourceDirs = [ "tests" ];
          mainPath = [ "doctests.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../contrib/network-3.1.2.1; }