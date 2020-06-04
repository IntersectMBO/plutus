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
      identifier = { name = "language-plutus-core"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "vanessa.mchale@iohk.io";
      author = "Vanessa McHale";
      homepage = "";
      url = "";
      synopsis = "Language library for Plutus Core";
      description = "Pretty-printer, parser, and typechecker for Plutus Core.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [
        "src/costModel.json"
        "language-plutus-core/src/costModel.json"
        ];
      extraTmpFiles = [];
      extraDocFiles = [ "README.md" ];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."array" or (buildDepError "array"))
          (hsPkgs."aeson" or (buildDepError "aeson"))
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."bimap" or (buildDepError "bimap"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."cardano-crypto" or (buildDepError "cardano-crypto"))
          (hsPkgs."cborg" or (buildDepError "cborg"))
          (hsPkgs."composition-prelude" or (buildDepError "composition-prelude"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."cryptonite" or (buildDepError "cryptonite"))
          (hsPkgs."dependent-map" or (buildDepError "dependent-map"))
          (hsPkgs."dependent-sum" or (buildDepError "dependent-sum"))
          (hsPkgs."dependent-sum-template" or (buildDepError "dependent-sum-template"))
          (hsPkgs."deriving-aeson" or (buildDepError "deriving-aeson"))
          (hsPkgs."deriving-compat" or (buildDepError "deriving-compat"))
          (hsPkgs."deepseq" or (buildDepError "deepseq"))
          (hsPkgs."filepath" or (buildDepError "filepath"))
          (hsPkgs."hashable" or (buildDepError "hashable"))
          (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."memory" or (buildDepError "memory"))
          (hsPkgs."mmorph" or (buildDepError "mmorph"))
          (hsPkgs."monoidal-containers" or (buildDepError "monoidal-containers"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          (hsPkgs."prettyprinter-configurable" or (buildDepError "prettyprinter-configurable"))
          (hsPkgs."recursion-schemes" or (buildDepError "recursion-schemes"))
          (hsPkgs."safe-exceptions" or (buildDepError "safe-exceptions"))
          (hsPkgs."semigroups" or (buildDepError "semigroups"))
          (hsPkgs."serialise" or (buildDepError "serialise"))
          (hsPkgs."tasty" or (buildDepError "tasty"))
          (hsPkgs."tasty-golden" or (buildDepError "tasty-golden"))
          (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."th-lift" or (buildDepError "th-lift"))
          (hsPkgs."th-lift-instances" or (buildDepError "th-lift-instances"))
          (hsPkgs."th-utilities" or (buildDepError "th-utilities"))
          (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
          (hsPkgs."transformers" or (buildDepError "transformers"))
          ];
        build-tools = [
          (hsPkgs.buildPackages.alex or (pkgs.buildPackages.alex or (buildToolDepError "alex")))
          (hsPkgs.buildPackages.happy or (pkgs.buildPackages.happy or (buildToolDepError "happy")))
          ];
        buildable = true;
        modules = [
          "Data/Aeson/THReader"
          "Language/PlutusCore/Pretty/ConfigName"
          "Language/PlutusCore/Core/Type"
          "Language/PlutusCore/Core/Plated"
          "Language/PlutusCore/Core/Instance/Eq"
          "Language/PlutusCore/Core/Instance/Pretty/Classic"
          "Language/PlutusCore/Core/Instance/Pretty/Common"
          "Language/PlutusCore/Core/Instance/Pretty/Default"
          "Language/PlutusCore/Core/Instance/Pretty/Plc"
          "Language/PlutusCore/Core/Instance/Pretty/Readable"
          "Language/PlutusCore/Core/Instance/Pretty"
          "Language/PlutusCore/Core/Instance/Recursive"
          "Language/PlutusCore/Core/Instance"
          "Language/PlutusCore/Constant/Apply"
          "Language/PlutusCore/Constant/Dynamic/BuiltinName"
          "Language/PlutusCore/Constant/Dynamic/Call"
          "Language/PlutusCore/Constant/Dynamic/Emit"
          "Language/PlutusCore/Constant/Dynamic/OnChain"
          "Language/PlutusCore/Constant/Dynamic/OffChain"
          "Language/PlutusCore/Constant/Function"
          "Language/PlutusCore/Constant/Name"
          "Language/PlutusCore/Constant/Typed"
          "Language/PlutusCore/Lexer/Type"
          "Language/PlutusCore/Eq"
          "Language/PlutusCore/Mark"
          "Language/PlutusCore/Pretty/Classic"
          "Language/PlutusCore/Pretty/ConfigName"
          "Language/PlutusCore/Pretty/Default"
          "Language/PlutusCore/Pretty/Plc"
          "Language/PlutusCore/Pretty/PrettyConst"
          "Language/PlutusCore/Pretty/Readable"
          "Language/PlutusCore/Pretty/Utils"
          "Language/PlutusCore/Universe/Core"
          "Language/PlutusCore/Universe/Default"
          "Language/PlutusCore/Error"
          "Language/PlutusCore/Size"
          "Language/PlutusCore/TypeCheck/Internal"
          "Language/PlutusCore/TypeCheck"
          "Language/PlutusCore/Analysis/Definitions"
          "Language/PlutusCore/Examples/Data/InterList"
          "Language/PlutusCore/Examples/Data/TreeForest"
          "Language/PlutusCore/Generators/Internal/Denotation"
          "Language/PlutusCore/Generators/Internal/Dependent"
          "Language/PlutusCore/Generators/Internal/Entity"
          "Language/PlutusCore/Generators/Internal/TypeEvalCheck"
          "Language/PlutusCore/Generators/Internal/TypedBuiltinGen"
          "Language/PlutusCore/Generators/Internal/Utils"
          "Data/Functor/Foldable/Monadic"
          "Language/PlutusCore"
          "Language/PlutusCore/Quote"
          "Language/PlutusCore/MkPlc"
          "Language/PlutusCore/Evaluation/Machine/Ck"
          "Language/PlutusCore/Evaluation/Machine/Cek"
          "Language/PlutusCore/Evaluation/Machine/ExBudgeting"
          "Language/PlutusCore/Evaluation/Machine/ExBudgetingDefaults"
          "Language/PlutusCore/Evaluation/Machine/Exception"
          "Language/PlutusCore/Evaluation/Machine/ExMemory"
          "Language/PlutusCore/Evaluation/Evaluator"
          "Language/PlutusCore/Evaluation/Result"
          "Language/PlutusCore/Check/Value"
          "Language/PlutusCore/Check/Normal"
          "Language/PlutusCore/CBOR"
          "Language/PlutusCore/Constant"
          "Language/PlutusCore/Constant/Dynamic"
          "Language/PlutusCore/Universe"
          "Language/PlutusCore/Rename/Internal"
          "Language/PlutusCore/Rename/Monad"
          "Language/PlutusCore/Rename"
          "Language/PlutusCore/Normalize"
          "Language/PlutusCore/Normalize/Internal"
          "Language/PlutusCore/Pretty"
          "Language/PlutusCore/View"
          "Language/PlutusCore/Subst"
          "Language/PlutusCore/Name"
          "Language/PlutusCore/Core"
          "Language/PlutusCore/DeBruijn"
          "Language/PlutusCore/Check/Uniques"
          "Language/PlutusCore/FsTree"
          "Language/PlutusCore/StdLib/Data/Bool"
          "Language/PlutusCore/StdLib/Data/ChurchNat"
          "Language/PlutusCore/StdLib/Data/Function"
          "Language/PlutusCore/StdLib/Data/Integer"
          "Language/PlutusCore/StdLib/Data/List"
          "Language/PlutusCore/StdLib/Data/Nat"
          "Language/PlutusCore/StdLib/Data/Sum"
          "Language/PlutusCore/StdLib/Data/Unit"
          "Language/PlutusCore/StdLib/Data/ScottUnit"
          "Language/PlutusCore/StdLib/Everything"
          "Language/PlutusCore/StdLib/Meta"
          "Language/PlutusCore/StdLib/Meta/Data/Tuple"
          "Language/PlutusCore/StdLib/Meta/Data/Function"
          "Language/PlutusCore/StdLib/Type"
          "Language/PlutusCore/Examples/Everything"
          "Language/PlutusCore/Generators"
          "Language/PlutusCore/Generators/AST"
          "Language/PlutusCore/Generators/Interesting"
          "Language/PlutusCore/Generators/Test"
          "Language/PlutusCore/Lexer"
          "Language/PlutusCore/Parser"
          "PlutusPrelude"
          "Common"
          "Data/ByteString/Lazy/Hash"
          "PlcTestUtils"
          "Crypto"
          "Data/Text/Prettyprint/Doc/Custom"
          ];
        hsSourceDirs = [
          "src"
          "prelude"
          "stdlib"
          "examples"
          "generators"
          "common"
          ];
        };
      exes = {
        "language-plutus-core-generate-evaluation-test" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."cborg" or (buildDepError "cborg"))
            (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."serialise" or (buildDepError "serialise"))
            (hsPkgs."text" or (buildDepError "text"))
            ];
          buildable = true;
          hsSourceDirs = [ "generate-evaluation-test" ];
          mainPath = [ "Main.hs" ];
          };
        "plc" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."serialise" or (buildDepError "serialise"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."optparse-applicative" or (buildDepError "optparse-applicative"))
            ];
          buildable = true;
          hsSourceDirs = [ "exe" ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "language-plutus-core-test" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."filepath" or (buildDepError "filepath"))
            (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."mmorph" or (buildDepError "mmorph"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."serialise" or (buildDepError "serialise"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-golden" or (buildDepError "tasty-golden"))
            (hsPkgs."tasty-hedgehog" or (buildDepError "tasty-hedgehog"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            (hsPkgs."tuple" or (buildDepError "tuple"))
            ];
          buildable = true;
          modules = [
            "Evaluation/ApplyBuiltinName"
            "Evaluation/DynamicBuiltins/Common"
            "Evaluation/DynamicBuiltins/Definition"
            "Evaluation/DynamicBuiltins/Logging"
            "Evaluation/DynamicBuiltins/MakeRead"
            "Evaluation/DynamicBuiltins"
            "Evaluation/Golden"
            "Evaluation/Machines"
            "Evaluation/Spec"
            "Normalization/Check"
            "Normalization/Type"
            "Pretty/Readable"
            "Check/Spec"
            "TypeSynthesis/Spec"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      benchmarks = {
        "language-plutus-core-bench" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."criterion" or (buildDepError "criterion"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."serialise" or (buildDepError "serialise"))
            ];
          buildable = true;
          hsSourceDirs = [ "bench" ];
          };
        "language-plutus-core-weigh" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."serialise" or (buildDepError "serialise"))
            (hsPkgs."weigh" or (buildDepError "weigh"))
            ];
          buildable = true;
          hsSourceDirs = [ "weigh" ];
          };
        "language-plutus-core-budgeting-bench" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."criterion" or (buildDepError "criterion"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."serialise" or (buildDepError "serialise"))
            (hsPkgs."deepseq" or (buildDepError "deepseq"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."directory" or (buildDepError "directory"))
            (hsPkgs."integer-gmp" or (buildDepError "integer-gmp"))
            ];
          buildable = true;
          hsSourceDirs = [ "budgeting-bench" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./language-plutus-core;
    }