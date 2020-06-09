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
      specVersion = "1.20";
      identifier = { name = "slack-web"; version = "0.2.0.12"; };
      license = "MIT";
      copyright = "2017 Juan Pedro Villa Isaza";
      maintainer = "Juan Pedro Villa Isaza <jpvillaisaza@gmail.com>";
      author = "Juan Pedro Villa Isaza <jpvillaisaza@gmail.com>";
      homepage = "https://github.com/jpvillaisaza/slack-web";
      url = "";
      synopsis = "Bindings for the Slack web API";
      description = "Haskell bindings for the Slack web API.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE.md" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [ "CHANGELOG.md" "README.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."http-api-data" or (errorHandler.buildDepError "http-api-data"))
          (hsPkgs."http-client" or (errorHandler.buildDepError "http-client"))
          (hsPkgs."http-client-tls" or (errorHandler.buildDepError "http-client-tls"))
          (hsPkgs."servant" or (errorHandler.buildDepError "servant"))
          (hsPkgs."servant-client" or (errorHandler.buildDepError "servant-client"))
          (hsPkgs."servant-client-core" or (errorHandler.buildDepError "servant-client-core"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
          (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
          ];
        buildable = true;
        modules = [
          "Web/Slack/Types"
          "Web/Slack/Util"
          "Web/Slack"
          "Web/Slack/Api"
          "Web/Slack/Auth"
          "Web/Slack/Channel"
          "Web/Slack/Chat"
          "Web/Slack/Common"
          "Web/Slack/Group"
          "Web/Slack/Im"
          "Web/Slack/MessageParser"
          "Web/Slack/User"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "tests" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
            (hsPkgs."hspec" or (errorHandler.buildDepError "hspec"))
            (hsPkgs."http-api-data" or (errorHandler.buildDepError "http-api-data"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
            ];
          buildable = true;
          modules = [
            "Web/Slack/MessageParser"
            "Web/Slack/MessageParserSpec"
            "Web/Slack/Types"
            ];
          hsSourceDirs = [ "src" "tests" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/4; }