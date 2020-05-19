let
  buildDepError = pkg:
    builtins.throw ''
      The Haskell package set does not contain the package: ${pkg} (build dependency).
      
      If you are using Stackage, make sure that you are using a snapshot that contains the package. Otherwise you may need to update the Hackage snapshot you are using, usually by updating haskell.nix.
      '';
  sysDepError = pkg:
    builtins.throw ''
      The Nixpkgs package set does not contain the package: ${pkg} (system dependency).
      
      You may need to augment the system package mapping in haskell.nix so that it can be found.
      '';
  pkgConfDepError = pkg:
    builtins.throw ''
      The pkg-conf packages does not contain the package: ${pkg} (pkg-conf dependency).
      
      You may need to augment the pkg-conf package mapping in haskell.nix so that it can be found.
      '';
  exeDepError = pkg:
    builtins.throw ''
      The local executable components do not include the component: ${pkg} (executable dependency).
      '';
  legacyExeDepError = pkg:
    builtins.throw ''
      The Haskell package set does not contain the package: ${pkg} (executable dependency).
      
      If you are using Stackage, make sure that you are using a snapshot that contains the package. Otherwise you may need to update the Hackage snapshot you are using, usually by updating haskell.nix.
      '';
  buildToolDepError = pkg:
    builtins.throw ''
      Neither the Haskell package set or the Nixpkgs package set contain the package: ${pkg} (build tool dependency).
      
      If this is a system dependency:
      You may need to augment the system package mapping in haskell.nix so that it can be found.
      
      If this is a Haskell dependency:
      If you are using Stackage, make sure that you are using a snapshot that contains the package. Otherwise you may need to update the Hackage snapshot you are using, usually by updating haskell.nix.
      '';
in { system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
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
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."nonempty-containers" or (buildDepError "nonempty-containers"))
          (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."mmorph" or (buildDepError "mmorph"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          (hsPkgs."recursion-schemes" or (buildDepError "recursion-schemes"))
          (hsPkgs."serialise" or (buildDepError "serialise"))
          (hsPkgs."semigroupoids" or (buildDepError "semigroupoids"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."transformers" or (buildDepError "transformers"))
          (hsPkgs."algebraic-graphs" or (buildDepError "algebraic-graphs"))
          (hsPkgs."megaparsec" or (buildDepError "megaparsec"))
          (hsPkgs."parser-combinators" or (buildDepError "parser-combinators"))
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
          "Language/PlutusIR/Transform/LetFloat"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "plutus-ir-test" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
            (hsPkgs."plutus-ir" or (buildDepError "plutus-ir"))
            (hsPkgs."filepath" or (buildDepError "filepath"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."mmorph" or (buildDepError "mmorph"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."serialise" or (buildDepError "serialise"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hedgehog" or (buildDepError "tasty-hedgehog"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."megaparsec" or (buildDepError "megaparsec"))
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