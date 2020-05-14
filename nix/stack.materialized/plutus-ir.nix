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
      specVersion = "2.0";
      identifier = { name = "plutus-ir"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones";
      homepage = "";
      url = "";
      synopsis = "Plutus IR language";
      description = "Plutus IR language library and compiler to Plutus Core.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [ "README.md" ];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."language-plutus-core" or (errorHandler.buildDepError "language-plutus-core"))
          (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."mmorph" or (errorHandler.buildDepError "mmorph"))
          (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
          (hsPkgs."recursion-schemes" or (errorHandler.buildDepError "recursion-schemes"))
          (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          (hsPkgs."algebraic-graphs" or (errorHandler.buildDepError "algebraic-graphs"))
          (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
          (hsPkgs."parser-combinators" or (errorHandler.buildDepError "parser-combinators"))
          ];
        buildable = true;
        modules = [
          "Language/PlutusIR/Analysis/Dependencies"
          "Language/PlutusIR/Analysis/Usages"
          "Language/PlutusIR/Compiler/Error"
          "Language/PlutusIR/Compiler/Let"
          "Language/PlutusIR/Compiler/Datatype"
          "Language/PlutusIR/Compiler/Provenance"
          "Language/PlutusIR/Compiler/Recursion"
          "Language/PlutusIR/Compiler/Types"
          "Language/PlutusIR/Compiler/Lower"
          "Language/PlutusIR"
          "Language/PlutusIR/Compiler"
          "Language/PlutusIR/Compiler/Names"
          "Language/PlutusIR/Compiler/Definitions"
          "Language/PlutusIR/Generators/AST"
          "Language/PlutusIR/Parser"
          "Language/PlutusIR/MkPir"
          "Language/PlutusIR/Value"
          "Language/PlutusIR/Optimizer/DeadCode"
          "Language/PlutusIR/Transform/Substitute"
          "Language/PlutusIR/Transform/ThunkRecursions"
          "Language/PlutusIR/Transform/Rename"
          "Language/PlutusIR/Transform/NonStrict"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "plutus-ir-test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
            (hsPkgs."plutus-ir" or (errorHandler.buildDepError "plutus-ir"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."language-plutus-core" or (errorHandler.buildDepError "language-plutus-core"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."mmorph" or (errorHandler.buildDepError "mmorph"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."serialise" or (errorHandler.buildDepError "serialise"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hedgehog" or (errorHandler.buildDepError "tasty-hedgehog"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
            ];
          buildable = true;
          modules = [ "OptimizerSpec" "TransformSpec" "ParserSpec" "TestLib" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-ir;
    }