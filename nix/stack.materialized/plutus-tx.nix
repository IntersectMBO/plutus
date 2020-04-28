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
      identifier = { name = "plutus-tx"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton Jones";
      homepage = "";
      url = "";
      synopsis = "Libraries for Plutus Tx and its prelude";
      description = "Libraries for Plutus Tx and its prelude";
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
          (hsPkgs."template-haskell" or (buildDepError "template-haskell"))
          (hsPkgs."th-abstraction" or (buildDepError "th-abstraction"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."plutus-ir" or (buildDepError "plutus-ir"))
          (hsPkgs."cborg" or (buildDepError "cborg"))
          (hsPkgs."serialise" or (buildDepError "serialise"))
          (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
          (hsPkgs."lens" or (buildDepError "lens"))
          ];
        build-tools = [
          (hsPkgs.buildPackages.doctest or (pkgs.buildPackages.doctest or (buildToolDepError "doctest")))
          ];
        buildable = true;
        modules = [
          "Language/PlutusTx/IsData/Instances"
          "Language/PlutusTx/IsData/TH"
          "Language/PlutusTx/Lift/THUtils"
          "Language/PlutusTx/Lift/Instances"
          "Language/PlutusTx"
          "Language/PlutusTx/TH"
          "Language/PlutusTx/Prelude"
          "Language/PlutusTx/Evaluation"
          "Language/PlutusTx/Applicative"
          "Language/PlutusTx/Bool"
          "Language/PlutusTx/IsData"
          "Language/PlutusTx/IsData/Class"
          "Language/PlutusTx/Eq"
          "Language/PlutusTx/Functor"
          "Language/PlutusTx/Lattice"
          "Language/PlutusTx/List"
          "Language/PlutusTx/Ord"
          "Language/PlutusTx/Maybe"
          "Language/PlutusTx/Numeric"
          "Language/PlutusTx/Ratio"
          "Language/PlutusTx/Semigroup"
          "Language/PlutusTx/Monoid"
          "Language/PlutusTx/AssocMap"
          "Language/PlutusTx/These"
          "Language/PlutusTx/Code"
          "Language/PlutusTx/Data"
          "Language/PlutusTx/Lift"
          "Language/PlutusTx/Lift/Class"
          "Language/PlutusTx/Builtins"
          "Language/PlutusTx/Plugin/Utils"
          "Language/PlutusTx/Utils"
          ];
        hsSourceDirs = [ "src" ];
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-tx;
    }