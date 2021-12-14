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
      identifier = { name = "lzma"; version = "0.0.0.3"; };
      license = "BSD-3-Clause";
      copyright = "(c) 2015, Herbert Valerio Riedel";
      maintainer = "hvr@gnu.org";
      author = "Herbert Valerio Riedel";
      homepage = "https://github.com/hvr/lzma";
      url = "";
      synopsis = "LZMA/XZ compression and decompression";
      description = "This package provides a pure interface for compressing and\ndecompressing\n<https://en.wikipedia.org/wiki/LZMA LZMA (Lempel–Ziv–Markov chain algorithm)>\nstreams of data represented as lazy @ByteString@s. A\nmonadic incremental interface is provided as well. This package\nrelies on the <http://tukaani.org/xz/ liblzma C library>.\n\nThe following packages are based on this package and provide\nAPI support for popular streaming frameworks:\n\n* </package/lzma-streams lzma-streams> (for </package/io-streams io-streams>)\n\n* </package/pipes-lzma pipes-lzma> (for </package/pipes pipes>)\n\n* </package/lzma-conduit lzma-conduit> (for </package/conduit conduit>)\n";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [ "Changelog.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          ] ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."lzma-clib" or (errorHandler.buildDepError "lzma-clib"));
        libs = (pkgs.lib).optional (!system.isWindows) (pkgs."lzma" or (errorHandler.sysDepError "lzma"));
        buildable = true;
        modules = [ "LibLzma" "Codec/Compression/Lzma" ];
        cSources = [ "cbits/lzma_wrapper.c" ];
        hsSourceDirs = [ "src" ];
        includes = (pkgs.lib).optional (!system.isWindows) "lzma.h";
        };
      tests = {
        "lzma-tests" = {
          depends = [
            (hsPkgs."lzma" or (errorHandler.buildDepError "lzma"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."HUnit" or (errorHandler.buildDepError "HUnit"))
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            ];
          buildable = true;
          hsSourceDirs = [ "src-tests" ];
          mainPath = [ "lzma-tests.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../contrib/lzma-0.0.0.3; }