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
    flags = {
      systemlib = false;
      fulltextsearch = true;
      urifilenames = true;
      haveusleep = true;
      json1 = true;
      };
    package = {
      specVersion = "1.10";
      identifier = { name = "direct-sqlite"; version = "2.3.26"; };
      license = "BSD-3-Clause";
      copyright = "Copyright (c) 2012 - 2014 Irene Knapp,\n2014 - 2018 Janne Hellsten,\n2018 - 2020 Sergey Bushnyak";
      maintainer = "Sergey Bushnyak <sergey.bushnyak@sigrlami.eu>";
      author = "Irene Knapp <irene.knapp@icloud.com>";
      homepage = "https://github.com/IreneKnapp/direct-sqlite";
      url = "";
      synopsis = "Low-level binding to SQLite3.  Includes UTF8 and BLOB support.";
      description = "This package is not very different from the other SQLite3 bindings out\nthere, but it fixes a few deficiencies I was finding.  As compared to\nbindings-sqlite3, it is slightly higher-level, in that it supports\nmarshalling of data values to and from the database.  In particular,\nit supports strings encoded as UTF8, and BLOBs represented as\nByteStrings.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [
        "cbits/sqlite3.c"
        "cbits/sqlite3.h"
        "cbits/sqlite3ext.h"
        "jsbits/emscripten/build.sh"
        "jsbits/emscripten/direct-sqlite-wrappers.js"
        "jsbits/emscripten/direct-sqlite.pre.js"
        "jsbits/emscripten/direct-sqlite.post.js"
        "changelog"
        ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."semigroups" or (errorHandler.buildDepError "semigroups"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          ];
        libs = if flags.systemlib
          then [ (pkgs."sqlite3" or (errorHandler.sysDepError "sqlite3")) ]
          else (pkgs.lib).optional (!system.isWindows && !system.isAndroid) (pkgs."pthread" or (errorHandler.sysDepError "pthread"));
        buildable = true;
        modules = [
          "Database/SQLite3"
          "Database/SQLite3/Bindings"
          "Database/SQLite3/Bindings/Types"
          "Database/SQLite3/Direct"
          ];
        cSources = (pkgs.lib).optional (!flags.systemlib) "cbits/sqlite3.c";
        jsSources = (pkgs.lib).optional (system.isGhcjs) "jsbits/direct-sqlite.js";
        includeDirs = [ "." ] ++ (pkgs.lib).optional (!flags.systemlib) "cbits";
        };
      tests = {
        "test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."HUnit" or (errorHandler.buildDepError "HUnit"))
            (hsPkgs."base16-bytestring" or (errorHandler.buildDepError "base16-bytestring"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."direct-sqlite" or (errorHandler.buildDepError "direct-sqlite"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            ];
          buildable = true;
          modules = [ "StrictEq" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../contrib/direct-sqlite-2.3.26; }