{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { eventlog = false; development = false; };
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
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.bytestring)
          (hsPkgs.cryptonite)
          (hsPkgs.containers)
          (hsPkgs.bimap)
          (hsPkgs.array)
          (hsPkgs.mtl)
          (hsPkgs.transformers)
          (hsPkgs.deepseq)
          (hsPkgs.recursion-schemes)
          (hsPkgs.text)
          (hsPkgs.prettyprinter)
          (hsPkgs.lens)
          (hsPkgs.composition-prelude)
          (hsPkgs.template-haskell)
          (hsPkgs.th-lift-instances)
          (hsPkgs.memory)
          (hsPkgs.mmorph)
          (hsPkgs.cborg)
          (hsPkgs.serialise)
          (hsPkgs.safe-exceptions)
          (hsPkgs.dependent-sum)
          (hsPkgs.dependent-map)
          (hsPkgs.hedgehog)
          (hsPkgs.filepath)
          (hsPkgs.tasty)
          (hsPkgs.tasty-golden)
          (hsPkgs.cryptonite)
          (hsPkgs.cardano-crypto)
          ];
        build-tools = [
          ((hsPkgs.buildPackages).alex)
          ((hsPkgs.buildPackages).happy)
          ];
        };
      exes = {
        "language-plutus-core-generate-evaluation-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.language-plutus-core)
            (hsPkgs.text)
            ];
          };
        };
      tests = {
        "language-plutus-core-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.language-plutus-core)
            (hsPkgs.tasty)
            (hsPkgs.hedgehog)
            (hsPkgs.tasty-hunit)
            (hsPkgs.tasty-hedgehog)
            (hsPkgs.transformers)
            (hsPkgs.bytestring)
            (hsPkgs.serialise)
            (hsPkgs.filepath)
            (hsPkgs.tasty-golden)
            (hsPkgs.text)
            (hsPkgs.prettyprinter)
            (hsPkgs.containers)
            (hsPkgs.mtl)
            (hsPkgs.mmorph)
            ];
          };
        };
      benchmarks = {
        "language-plutus-core-bench" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.language-plutus-core)
            (hsPkgs.criterion)
            (hsPkgs.bytestring)
            (hsPkgs.serialise)
            (hsPkgs.text)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././language-plutus-core; }