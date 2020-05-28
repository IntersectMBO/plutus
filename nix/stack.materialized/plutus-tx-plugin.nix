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
      specVersion = "2.2";
      identifier = { name = "plutus-tx-plugin"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones";
      homepage = "";
      url = "";
      synopsis = "The Plutus Tx compiler and GHC plugin";
      description = "The Plutus Tx compiler and GHC plugin.";
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
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."extra" or (buildDepError "extra"))
          (hsPkgs."ghc" or (buildDepError "ghc"))
          (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."plutus-ir" or (buildDepError "plutus-ir"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          (hsPkgs."serialise" or (buildDepError "serialise"))
          (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."transformers" or (buildDepError "transformers"))
          (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
          ];
        buildable = true;
        modules = [
          "Language/PlutusTx/PLCTypes"
          "Language/PlutusTx/PIRTypes"
          "Language/PlutusTx/Compiler/Error"
          "Language/PlutusTx/Compiler/Binders"
          "Language/PlutusTx/Compiler/Builtins"
          "Language/PlutusTx/Compiler/Laziness"
          "Language/PlutusTx/Compiler/Expr"
          "Language/PlutusTx/Compiler/Names"
          "Language/PlutusTx/Compiler/Kind"
          "Language/PlutusTx/Compiler/Primitives"
          "Language/PlutusTx/Compiler/Type"
          "Language/PlutusTx/Compiler/Types"
          "Language/PlutusTx/Compiler/Utils"
          "Language/PlutusTx/Plugin"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "plutus-tx-tests" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."integer-gmp" or (buildDepError "integer-gmp"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"))
            (hsPkgs."plutus-ir" or (buildDepError "plutus-ir"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."serialise" or (buildDepError "serialise"))
            (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."tasty-hedgehog" or (buildDepError "tasty-hedgehog"))
            (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
            (hsPkgs."lens" or (buildDepError "lens"))
            ];
          buildable = true;
          modules = [
            "Lift/Spec"
            "Plugin/Spec"
            "Plugin/Basic/Spec"
            "Plugin/Data/Spec"
            "Plugin/Errors/Spec"
            "Plugin/Functions/Spec"
            "Plugin/Laziness/Spec"
            "Plugin/Primitives/Spec"
            "Plugin/Typeclasses/Spec"
            "Plugin/Typeclasses/Lib"
            "Plugin/Lib"
            "StdLib/Spec"
            "TH/Spec"
            "TH/TestTH"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-tx-plugin;
    }