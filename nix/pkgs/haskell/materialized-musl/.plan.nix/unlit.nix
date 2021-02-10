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
      identifier = { name = "unlit"; version = "0.4.0.1"; };
      license = "BSD-3-Clause";
      copyright = "2014 (c) Wen Kokke";
      maintainer = "wen.kokke@gmail.com";
      author = "Wen Kokke";
      homepage = "";
      url = "";
      synopsis = "Tool to convert literate code between styles or to code.";
      description = "Tool to convert literate code between styles or to code.\nUsage:\n\n> unlit\n>   -f STYLE_NAME  --from=STYLE_NAME    Source style (all, bird, haskell, latex, markdown, tildefence, backtickfence)\n>   -t STYLE_NAME  --to=STYLE_NAME      Target style (bird, latex, tildefence, backtickfence, code)\n>   -i FILE        --input=FILE         Input file (optional)\n>   -o FILE        --output=FILE        Output file (optional)\n>   -l LANGUAGE    --language=LANGUAGE  Programming language (restrict fenced code blocks)\n>   -h             --help               Show help\n>   -v             --version            Show version\n";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          ];
        buildable = true;
        modules = [ "Unlit/Text" "Unlit/String" ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "unlit" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."unlit" or (errorHandler.buildDepError "unlit"))
            ];
          buildable = true;
          hsSourceDirs = [ "exe" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/3; }