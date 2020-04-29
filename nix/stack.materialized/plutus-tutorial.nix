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
    flags = { defer-plugin-errors = false; };
    package = {
      specVersion = "2.2";
      identifier = { name = "plutus-tutorial"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "jann.mueller@iohk.io";
      author = "Michael Peyton Jones, Jann Mueller";
      homepage = "";
      url = "";
      synopsis = "PlutusTx tutorial";
      description = "A tutorial for PlutusTx.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [ "README.adoc" ];
      };
    components = {
      exes = {
        "tutorial-doctests" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."plutus-tx" or (buildDepError "plutus-tx"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."plutus-emulator" or (buildDepError "plutus-emulator"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."containers" or (buildDepError "containers"))
            ] ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) (hsPkgs."plutus-tx-plugin" or (buildDepError "plutus-tx-plugin"));
          build-tools = [
            (hsPkgs.buildPackages.unlit or (pkgs.buildPackages.unlit or (buildToolDepError "unlit")))
            (hsPkgs.buildPackages.doctest or (pkgs.buildPackages.doctest or (buildToolDepError "doctest")))
            ];
          buildable = true;
          modules = [ "Tutorial/PlutusTx" ];
          hsSourceDirs = [ "doctest" "doc" ];
          mainPath = ([
            "Main.hs"
            ] ++ (pkgs.lib).optional (flags.defer-plugin-errors) "") ++ (pkgs.lib).optional (!(compiler.isGhcjs && true || system.isGhcjs)) "";
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-tutorial;
    }