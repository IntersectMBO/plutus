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
    flags = { developer = false; };
    package = {
      specVersion = "1.8";
      identifier = { name = "double-conversion"; version = "2.0.2.0"; };
      license = "BSD-3-Clause";
      copyright = "";
      maintainer = "Bryan O'Sullivan <bos@serpentine.com>";
      author = "Bryan O'Sullivan <bos@serpentine.com>";
      homepage = "https://github.com/bos/double-conversion";
      url = "";
      synopsis = "Fast conversion between double precision floating point and text";
      description = "A library that performs fast, accurate conversion between double\nprecision floating point and text.\n\nThis library is implemented as bindings to the C++\n@double-conversion@ library written by Florian Loitsch at Google:\n<https://github.com/floitsch/double-conversion>.\n\nThe 'Text' versions of these functions are about 30 times faster\nthan the default 'show' implementation for the 'Double' type.\n\nThe 'ByteString' versions are /slower/ than the 'Text' versions;\nroughly half the speed.  (This seems to be due to the cost of\nallocating 'ByteString' values via @malloc@.)\n\nAs a final note, be aware that the @bytestring-show@ package is\nabout 50% slower than simply using 'show'.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [
        "README.markdown"
        "benchmarks/*.cabal"
        "benchmarks/*.hs"
        "double-conversion/*.cmake.in"
        "double-conversion/AUTHORS"
        "double-conversion/CMakeLists.txt"
        "double-conversion/COPYING"
        "double-conversion/Changelog"
        "double-conversion/LICENSE"
        "double-conversion/Makefile"
        "double-conversion/README"
        "double-conversion/SConstruct"
        "double-conversion/src/*.cc"
        "double-conversion/src/*.h"
        "double-conversion/src/CMakeLists.txt"
        "double-conversion/src/SConscript"
        "double-conversion/test/CMakeLists.txt"
        "double-conversion/test/cctest/*.cc"
        "double-conversion/test/cctest/*.h"
        "double-conversion/test/cctest/CMakeLists.txt"
        "double-conversion/test/cctest/SConscript"
        "include/*.h"
        "tests/*.hs"
        ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."ghc-prim" or (errorHandler.buildDepError "ghc-prim"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          ];
        buildable = true;
        modules = [
          "Data/Double/Conversion/ByteString"
          "Data/Double/Conversion/Text"
          ];
        includeDirs = [ "double-conversion/src" "include" ];
        };
      tests = {
        "tests" = {
          depends = [
            (hsPkgs."HUnit" or (errorHandler.buildDepError "HUnit"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."double-conversion" or (errorHandler.buildDepError "double-conversion"))
            (hsPkgs."test-framework" or (errorHandler.buildDepError "test-framework"))
            (hsPkgs."test-framework-hunit" or (errorHandler.buildDepError "test-framework-hunit"))
            (hsPkgs."test-framework-quickcheck2" or (errorHandler.buildDepError "test-framework-quickcheck2"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            ];
          buildable = true;
          modules = [ "Regressions" ];
          hsSourceDirs = [ "tests" ];
          mainPath = [ "Properties.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ../contrib/double-conversion-2.0.2.0;
    }