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
      specVersion = "2.4";
      identifier = { name = "ghcjs-c-interop"; version = "0.1.0.0"; };
      license = "NONE";
      copyright = "";
      maintainer = "moritz.angermann@gmail.com";
      author = "Moritz Angermann";
      homepage = "";
      url = "";
      synopsis = "";
      description = "";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [
        "CHANGELOG.md"
        "jsbits/emscripten/build.sh"
        "jsbits/emscripten/test-cbits.pre.js"
        "jsbits/emscripten/test-cbits.post.js"
        "jsbits/emscripten/test-wrappers.js"
        "jsbits/emscripten/extern.js"
        ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [ (hsPkgs."base" or (errorHandler.buildDepError "base")) ];
        buildable = true;
        modules = [ "Test" ];
        cSources = [ "cbits/test.c" ];
        jsSources = [ "jsbits/test.js" ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "ghcjs-c-interop" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."ghcjs-c-interop" or (errorHandler.buildDepError "ghcjs-c-interop"))
            ];
          buildable = true;
          hsSourceDirs = [ "app" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../contrib/ghcjs-c-interop; }