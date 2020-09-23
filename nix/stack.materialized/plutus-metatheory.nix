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
      specVersion = "2.4";
      identifier = { name = "plutus-metatheory"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "james.chapman@iohk.io";
      author = "James Chapman";
      homepage = "https://github.com/input-output-hk/plutus";
      url = "";
      synopsis = "Command line tool for running plutus core programs";
      description = "";
      buildType = "Custom";
      isLocal = true;
      setup-depends = [
        (hsPkgs.buildPackages.base or (pkgs.buildPackages.base or (errorHandler.buildToolDepError "base")))
        (hsPkgs.buildPackages.Cabal or (pkgs.buildPackages.Cabal or (errorHandler.buildToolDepError "Cabal")))
        (hsPkgs.buildPackages.process or (pkgs.buildPackages.process or (errorHandler.buildToolDepError "process")))
        (hsPkgs.buildPackages.turtle or (pkgs.buildPackages.turtle or (errorHandler.buildToolDepError "turtle")))
        ];
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [ "README.md" "Plutus.agda-lib" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
          (hsPkgs."ieee754" or (errorHandler.buildDepError "ieee754"))
          (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
          (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
          (hsPkgs."process" or (errorHandler.buildDepError "process"))
          (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          ];
        buildable = true;
        modules = [
          "Raw"
          "Scoped"
          "Opts"
          "MAlonzo/Code/Main"
          "MAlonzo/Code/Agda/Builtin/Bool"
          "MAlonzo/Code/Agda/Builtin/Char"
          "MAlonzo/Code/Agda/Builtin/Equality"
          "MAlonzo/Code/Agda/Builtin/IO"
          "MAlonzo/Code/Agda/Builtin/Int"
          "MAlonzo/Code/Agda/Builtin/List"
          "MAlonzo/Code/Agda/Builtin/Nat"
          "MAlonzo/Code/Agda/Builtin/Sigma"
          "MAlonzo/Code/Agda/Builtin/String"
          "MAlonzo/Code/Agda/Builtin/Unit"
          "MAlonzo/Code/Agda/Primitive"
          "MAlonzo/Code/Algebra"
          "MAlonzo/Code/Algebra/Consequences/Base"
          "MAlonzo/Code/Algebra/Consequences/Setoid"
          "MAlonzo/Code/Algebra/Morphism"
          "MAlonzo/Code/Algebra/Properties/BooleanAlgebra"
          "MAlonzo/Code/Algebra/Properties/DistributiveLattice"
          "MAlonzo/Code/Algebra/Properties/Lattice"
          "MAlonzo/Code/Algebra/Properties/Semilattice"
          "MAlonzo/Code/Algebra/Structures"
          "MAlonzo/Code/Builtin"
          "MAlonzo/Code/Builtin/Constant/Term"
          "MAlonzo/Code/Builtin/Constant/Type"
          "MAlonzo/Code/Builtin/Signature"
          "MAlonzo/Code/Category/Applicative/Indexed"
          "MAlonzo/Code/Category/Functor"
          "MAlonzo/Code/Category/Monad/Indexed"
          "MAlonzo/Code/Data/Bool/Base"
          "MAlonzo/Code/Data/Bool/Properties"
          "MAlonzo/Code/Data/Char/Properties"
          "MAlonzo/Code/Data/Digit"
          "MAlonzo/Code/Data/Empty"
          "MAlonzo/Code/Data/Empty/Irrelevant"
          "MAlonzo/Code/Data/Fin/Base"
          "MAlonzo/Code/Data/Integer"
          "MAlonzo/Code/Data/Integer/Base"
          "MAlonzo/Code/Data/Integer/Properties"
          "MAlonzo/Code/Data/List/Base"
          "MAlonzo/Code/Data/List/NonEmpty"
          "MAlonzo/Code/Data/List/Properties"
          "MAlonzo/Code/Data/List/Relation/Binary/Lex/Core"
          "MAlonzo/Code/Data/List/Relation/Binary/Lex/Strict"
          "MAlonzo/Code/Data/List/Relation/Binary/Pointwise"
          "MAlonzo/Code/Data/List/Relation/Unary/All"
          "MAlonzo/Code/Data/List/Relation/Unary/Any"
          "MAlonzo/Code/Data/Maybe/Base"
          "MAlonzo/Code/Data/Nat/Base"
          "MAlonzo/Code/Data/Nat/DivMod"
          "MAlonzo/Code/Data/Nat/DivMod/Core"
          "MAlonzo/Code/Data/Nat/Properties"
          "MAlonzo/Code/Data/Nat/Show"
          "MAlonzo/Code/Data/Product"
          "MAlonzo/Code/Data/Sign"
          "MAlonzo/Code/Data/String/Base"
          "MAlonzo/Code/Data/String/Properties"
          "MAlonzo/Code/Data/Sum/Base"
          "MAlonzo/Code/Data/Vec"
          "MAlonzo/Code/Function/Bijection"
          "MAlonzo/Code/Function/Equality"
          "MAlonzo/Code/Function/Equivalence"
          "MAlonzo/Code/Function/Injection"
          "MAlonzo/Code/Function/Inverse"
          "MAlonzo/Code/Function/LeftInverse"
          "MAlonzo/Code/Function/Surjection"
          "MAlonzo/Code/Induction"
          "MAlonzo/Code/Induction/WellFounded"
          "MAlonzo/Code/Level"
          "MAlonzo/Code/Raw"
          "MAlonzo/Code/Relation/Binary"
          "MAlonzo/Code/Relation/Binary/Consequences"
          "MAlonzo/Code/Relation/Binary/Construct/NaturalOrder/Left"
          "MAlonzo/Code/Relation/Binary/Construct/NonStrictToStrict"
          "MAlonzo/Code/Relation/Binary/Construct/On"
          "MAlonzo/Code/Relation/Binary/Core"
          "MAlonzo/Code/Relation/Binary/Indexed/Heterogeneous"
          "MAlonzo/Code/Relation/Binary/Indexed/Heterogeneous/Construct/Trivial"
          "MAlonzo/Code/Relation/Binary/Lattice"
          "MAlonzo/Code/Relation/Binary/Properties/Poset"
          "MAlonzo/Code/Relation/Binary/Properties/Preorder"
          "MAlonzo/Code/Relation/Binary/PropositionalEquality"
          "MAlonzo/Code/Relation/Binary/PropositionalEquality/Core"
          "MAlonzo/Code/Relation/Binary/Reasoning/Base/Single"
          "MAlonzo/Code/Relation/Binary/Reasoning/Base/Triple"
          "MAlonzo/Code/Relation/Binary/Reasoning/Setoid"
          "MAlonzo/Code/Relation/Nullary"
          "MAlonzo/Code/Relation/Nullary/Decidable"
          "MAlonzo/Code/Relation/Nullary/Negation"
          "MAlonzo/Code/Relation/Nullary/Product"
          "MAlonzo/Code/Relation/Nullary/Sum"
          "MAlonzo/Code/Relation/Unary/Properties"
          "MAlonzo/Code/Algebra/Bundles"
          "MAlonzo/Code/Data/Nat/Divisibility/Core"
          "MAlonzo/Code/Data/Sign/Base"
          "MAlonzo/Code/Data/These/Base"
          "MAlonzo/Code/Data/Vec/Base"
          "MAlonzo/Code/Data/Vec/Bounded/Base"
          "MAlonzo/Code/Relation/Binary/Bundles"
          "MAlonzo/Code/Relation/Binary/Definitions"
          "MAlonzo/Code/Relation/Binary/Indexed/Heterogeneous/Bundles"
          "MAlonzo/Code/Relation/Binary/Indexed/Heterogeneous/Structures"
          "MAlonzo/Code/Relation/Binary/Reasoning/Base/Partial"
          "MAlonzo/Code/Relation/Binary/Reasoning/PartialSetoid"
          "MAlonzo/Code/Relation/Binary/Structures"
          "MAlonzo/Code/Relation/Nullary/Decidable/Core"
          "MAlonzo/Code/Relation/Nullary/Reflects"
          "MAlonzo/Code/Scoped"
          "MAlonzo/Code/Scoped/Reduction"
          "MAlonzo/Code/Scoped/RenamingSubstitution"
          "MAlonzo/Code/Type"
          "MAlonzo/Code/Utils"
          "MAlonzo/RTE"
          "MAlonzo/Code/Algorithmic"
          "MAlonzo/Code/Algorithmic/CK"
          "MAlonzo/Code/Algorithmic/CEKC"
          "MAlonzo/Code/Algorithmic/CEKV"
          "MAlonzo/Code/Check"
          "MAlonzo/Code/Scoped/CK"
          "MAlonzo/Code/Scoped/Extrication"
          "MAlonzo/Code/Type/BetaNBE"
          "MAlonzo/Code/Type/BetaNBE/Completeness"
          "MAlonzo/Code/Type/BetaNBE/Soundness"
          "MAlonzo/Code/Type/BetaNBE/Stability"
          "MAlonzo/Code/Type/BetaNBE/RenamingSubstitution"
          "MAlonzo/Code/Type/BetaNormal"
          "MAlonzo/Code/Type/BetaNormal/Equality"
          "MAlonzo/Code/Type/Equality"
          "MAlonzo/Code/Type/RenamingSubstitution"
          "MAlonzo/Code/Algorithmic/Reduction"
          "MAlonzo/Code/Algorithmic/RenamingSubstitution"
          "MAlonzo/Code/Scoped/Erasure"
          "MAlonzo/Code/Untyped"
          "MAlonzo/Code/Untyped/Reduction"
          "MAlonzo/Code/Untyped/RenamingSubstitution"
          "MAlonzo/Code/Algebra/Construct/LiftedChoice"
          "MAlonzo/Code/Algebra/Construct/NaturalChoice/Min"
          "MAlonzo/Code/Algebra/Structures/Biased"
          "MAlonzo/Code/Data/List/Categorical"
          "MAlonzo/Code/Data/List/Extrema"
          "MAlonzo/Code/Data/List/Extrema/Core"
          "MAlonzo/Code/Data/List/Membership/DecSetoid"
          "MAlonzo/Code/Data/List/Membership/Propositional"
          "MAlonzo/Code/Data/List/Membership/Propositional/Properties"
          "MAlonzo/Code/Data/List/Membership/Propositional/Properties/Core"
          "MAlonzo/Code/Data/List/Membership/Setoid"
          "MAlonzo/Code/Data/List/Membership/Setoid/Properties"
          "MAlonzo/Code/Data/List/Relation/Binary/Equality/Propositional"
          "MAlonzo/Code/Data/List/Relation/Binary/Equality/Setoid"
          "MAlonzo/Code/Data/List/Relation/Unary/All/Properties"
          "MAlonzo/Code/Data/List/Relation/Unary/AllPairs/Core"
          "MAlonzo/Code/Data/List/Relation/Unary/Any/Properties"
          "MAlonzo/Code/Data/Maybe/Relation/Unary/All"
          "MAlonzo/Code/Data/Maybe/Relation/Unary/Any"
          "MAlonzo/Code/Data/Product/Function/Dependent/Propositional"
          "MAlonzo/Code/Data/Product/Function/NonDependent/Propositional"
          "MAlonzo/Code/Data/Product/Function/NonDependent/Setoid"
          "MAlonzo/Code/Data/Product/Properties"
          "MAlonzo/Code/Data/Product/Relation/Binary/Pointwise/NonDependent"
          "MAlonzo/Code/Data/Sum/Function/Propositional"
          "MAlonzo/Code/Data/Sum/Function/Setoid"
          "MAlonzo/Code/Data/Sum/Relation/Binary/Pointwise"
          "MAlonzo/Code/Function/HalfAdjointEquivalence"
          "MAlonzo/Code/Function/Related"
          "MAlonzo/Code/Function/Related/TypeIsomorphisms"
          "MAlonzo/Code/Relation/Binary/Construct/Converse"
          "MAlonzo/Code/Agda/Builtin/Coinduction"
          "MAlonzo/Code/Agda/Builtin/Size"
          "MAlonzo/Code/Codata/Colist"
          "MAlonzo/Code/Codata/Conat"
          "MAlonzo/Code/Codata/Cowriter"
          "MAlonzo/Code/Codata/Delay"
          "MAlonzo/Code/Codata/Musical/Colist"
          "MAlonzo/Code/Codata/Musical/Conat"
          "MAlonzo/Code/Codata/Stream"
          "MAlonzo/Code/Codata/Thunk"
          "MAlonzo/Code/Data/BoundedVec"
          "MAlonzo/Code/Data/BoundedVec/Inefficient"
          "MAlonzo/Code/IO/Primitive"
          "MAlonzo/Code/Relation/Binary/Construct/FromRel"
          "MAlonzo/Code/Relation/Binary/Reasoning/Base/Double"
          ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "plc-agda" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-metatheory" or (errorHandler.buildDepError "plutus-metatheory"))
            ];
          buildable = true;
          hsSourceDirs = [ "exe" ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "test1" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."plutus-metatheory" or (errorHandler.buildDepError "plutus-metatheory"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.plutus-core or (pkgs.buildPackages.plutus-core or (errorHandler.buildToolDepError "plutus-core")))
            ];
          buildable = true;
          hsSourceDirs = [ "test" ];
          mainPath = [ "TestSimple.hs" ];
          };
        "test2" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."Cabal" or (errorHandler.buildDepError "Cabal"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."plutus-metatheory" or (errorHandler.buildDepError "plutus-metatheory"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.plutus-core or (pkgs.buildPackages.plutus-core or (errorHandler.buildToolDepError "plutus-core")))
            ];
          buildable = true;
          hsSourceDirs = [ "test" ];
          };
        "test3" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."lazy-search" or (errorHandler.buildDepError "lazy-search"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."plutus-metatheory" or (errorHandler.buildDepError "plutus-metatheory"))
            (hsPkgs."plutus-core" or (errorHandler.buildDepError "plutus-core"))
            (hsPkgs."size-based" or (errorHandler.buildDepError "size-based"))
            (hsPkgs."Stream" or (errorHandler.buildDepError "Stream"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            ];
          buildable = true;
          hsSourceDirs = [ "test" ];
          mainPath = [ "TestNEAT.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./plutus-metatheory;
    }