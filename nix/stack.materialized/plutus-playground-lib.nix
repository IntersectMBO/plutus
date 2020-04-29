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
      identifier = { name = "plutus-playground-lib"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "2018 IOHK";
      maintainer = "kris.jenkins@tweag.io";
      author = "Kris Jenkins";
      homepage = "https://github.com/iohk/plutus#readme";
      url = "";
      synopsis = "";
      description = "Please see the README on GitHub at <https://github.com/input-output-hk/plutus#readme>";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."aeson" or (buildDepError "aeson"))
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."cryptonite" or (buildDepError "cryptonite"))
          (hsPkgs."freer-simple" or (buildDepError "freer-simple"))
          (hsPkgs."deriving-compat" or (buildDepError "deriving-compat"))
          (hsPkgs."unordered-containers" or (buildDepError "unordered-containers"))
          (hsPkgs."insert-ordered-containers" or (buildDepError "insert-ordered-containers"))
          (hsPkgs."iots-export" or (buildDepError "iots-export"))
          (hsPkgs."playground-common" or (buildDepError "playground-common"))
          (hsPkgs."recursion-schemes" or (buildDepError "recursion-schemes"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."memory" or (buildDepError "memory"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."newtype-generics" or (buildDepError "newtype-generics"))
          (hsPkgs."row-types" or (buildDepError "row-types"))
          (hsPkgs."servant" or (buildDepError "servant"))
          (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."transformers" or (buildDepError "transformers"))
          (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
          (hsPkgs."plutus-contract-tasty" or (buildDepError "plutus-contract-tasty"))
          (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
          (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
          (hsPkgs."plutus-emulator" or (buildDepError "plutus-emulator"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          (hsPkgs."serialise" or (buildDepError "serialise"))
          (hsPkgs."wl-pprint-text" or (buildDepError "wl-pprint-text"))
          ];
        buildable = true;
        modules = [
          "Playground/Schema"
          "Playground/Contract"
          "Playground/API"
          "Playground/Types"
          "Playground/TH"
          "Playground/Interpreter/Util"
          "Schema"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "plutus-playground-lib-test" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."hedgehog" or (buildDepError "hedgehog"))
            (hsPkgs."iots-export" or (buildDepError "iots-export"))
            (hsPkgs."playground-common" or (buildDepError "playground-common"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
            (hsPkgs."plutus-playground-lib" or (buildDepError "plutus-playground-lib"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."plutus-emulator" or (buildDepError "plutus-emulator"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."recursion-schemes" or (buildDepError "recursion-schemes"))
            (hsPkgs."QuickCheck" or (buildDepError "QuickCheck"))
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."freer-simple" or (buildDepError "freer-simple"))
            ];
          buildable = true;
          modules = [ "Playground/THSpec" "Playground/TypesSpec" "SchemaSpec" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-playground-lib;
    }