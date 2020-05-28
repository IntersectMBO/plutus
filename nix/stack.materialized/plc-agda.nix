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
      specVersion = "2.4";
      identifier = { name = "plc-agda"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "james.chapman@iohk.io";
      author = "James Chapman";
      homepage = "https://github.com/input-output-hk/plutus";
      url = "";
      synopsis = "Command line tool for running plutus core programs";
      description = "";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [ "README.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      exes = {
        "plc-agda" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."ieee754" or (buildDepError "ieee754"))
            (hsPkgs."cryptonite" or (buildDepError "cryptonite"))
            (hsPkgs."memory" or (buildDepError "memory"))
            (hsPkgs."optparse-applicative" or (buildDepError "optparse-applicative"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
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
            "MAlonzo/Code/Algebra/FunctionProperties/Consequences"
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
            "MAlonzo/Code/Data/These"
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
            ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "test-plc-agda" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."process" or (buildDepError "process"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."ieee754" or (buildDepError "ieee754"))
            (hsPkgs."cryptonite" or (buildDepError "cryptonite"))
            (hsPkgs."memory" or (buildDepError "memory"))
            (hsPkgs."optparse-applicative" or (buildDepError "optparse-applicative"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.language-plutus-core or (pkgs.buildPackages.language-plutus-core or (buildToolDepError "language-plutus-core")))
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
            "MAlonzo/Code/Algebra/FunctionProperties/Consequences"
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
            "MAlonzo/Code/Data/These"
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
            ];
          mainPath = [ "TestSimple.hs" ];
          };
        "test2-plc-agda" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."Cabal" or (buildDepError "Cabal"))
            (hsPkgs."process" or (buildDepError "process"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."ieee754" or (buildDepError "ieee754"))
            (hsPkgs."cryptonite" or (buildDepError "cryptonite"))
            (hsPkgs."memory" or (buildDepError "memory"))
            (hsPkgs."optparse-applicative" or (buildDepError "optparse-applicative"))
            (hsPkgs."language-plutus-core" or (buildDepError "language-plutus-core"))
            (hsPkgs."directory" or (buildDepError "directory"))
            (hsPkgs."transformers" or (buildDepError "transformers"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.language-plutus-core or (pkgs.buildPackages.language-plutus-core or (buildToolDepError "language-plutus-core")))
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
            "MAlonzo/Code/Algebra/FunctionProperties/Consequences"
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
            "MAlonzo/Code/Data/These"
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
            "MAlonzo/Code/Scoped"
            "MAlonzo/Code/Scoped/Reduction"
            "MAlonzo/Code/Scoped/RenamingSubstitution"
            "MAlonzo/Code/Type"
            "MAlonzo/Code/Utils"
            "MAlonzo/RTE"
            "MAlonzo/Code/Algorithmic"
            "MAlonzo/Code/Algorithmic/CK"
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
            ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./metatheory;
    }