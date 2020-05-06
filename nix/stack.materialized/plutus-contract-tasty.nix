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
      identifier = { name = "plutus-contract-tasty"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "jann.mueller@iohk.io";
      author = "Jann Müller";
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
          (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
          (hsPkgs."plutus-emulator" or (buildDepError "plutus-emulator"))
          (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
          (hsPkgs."iots-export" or (buildDepError "iots-export"))
          (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
          (hsPkgs."aeson" or (buildDepError "aeson"))
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."semigroupoids" or (buildDepError "semigroupoids"))
          (hsPkgs."profunctors" or (buildDepError "profunctors"))
          (hsPkgs."transformers-base" or (buildDepError "transformers-base"))
          (hsPkgs."monad-control" or (buildDepError "monad-control"))
          (hsPkgs."mmorph" or (buildDepError "mmorph"))
          (hsPkgs."tasty" or (buildDepError "tasty"))
          (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
          (hsPkgs."row-types" or (buildDepError "row-types"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          ];
        buildable = true;
        modules = [ "Language/Plutus/Contract/Test" ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "plutus-contract-tasty-test" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            (hsPkgs."extensible-effects" or (buildDepError "extensible-effects"))
            (hsPkgs."plutus-emulator" or (buildDepError "plutus-emulator"))
            (hsPkgs."plutus-contract" or (buildDepError "plutus-contract"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."plutus-contract-tasty" or (buildDepError "plutus-contract-tasty"))
            ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"));
          buildable = true;
          modules = [ "Spec/Contract" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-contract-tasty;
    }