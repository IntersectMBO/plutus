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
      specVersion = "1.10";
      identifier = {
        name = "prettyprinter-configurable";
        version = "0.1.0.0";
        };
      license = "NONE";
      copyright = "";
      maintainer = "plutus@iohk.io";
      author = "David Luposchainsky, effectfully";
      homepage = "";
      url = "";
      synopsis = "";
      description = "";
      buildType = "Custom";
      isLocal = true;
      setup-depends = [
        (hsPkgs.buildPackages.base or (pkgs.buildPackages.base or (buildToolDepError "base")))
        (hsPkgs.buildPackages.Cabal or (pkgs.buildPackages.Cabal or (buildToolDepError "Cabal")))
        (hsPkgs.buildPackages.cabal-doctest or (pkgs.buildPackages.cabal-doctest or (buildToolDepError "cabal-doctest")))
        ];
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [ "README.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."microlens" or (buildDepError "microlens"))
          ];
        buildable = true;
        modules = [
          "Text/Fixity"
          "Text/Fixity/Internal"
          "Text/Pretty"
          "Text/PrettyBy"
          "Text/PrettyBy/Default"
          "Text/PrettyBy/Fixity"
          "Text/PrettyBy/Internal"
          "Text/PrettyBy/Internal/Utils"
          "Text/PrettyBy/Monad"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "prettyprinter-configurable-test" = {
          depends = [
            (hsPkgs."prettyprinter-configurable" or (buildDepError "prettyprinter-configurable"))
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."prettyprinter" or (buildDepError "prettyprinter"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."megaparsec" or (buildDepError "megaparsec"))
            (hsPkgs."parser-combinators" or (buildDepError "parser-combinators"))
            (hsPkgs."doctest" or (buildDepError "doctest"))
            (hsPkgs."QuickCheck" or (buildDepError "QuickCheck"))
            (hsPkgs."quickcheck-text" or (buildDepError "quickcheck-text"))
            (hsPkgs."tasty" or (buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (buildDepError "tasty-hunit"))
            (hsPkgs."tasty-quickcheck" or (buildDepError "tasty-quickcheck"))
            ];
          buildable = true;
          modules = [ "Default" "NonDefault" "Universal" "Expr" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Main.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./prettyprinter-configurable;
    }
