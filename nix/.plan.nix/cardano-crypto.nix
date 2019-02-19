{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { golden-tests = false; golden-tests-exe = false; };
    package = {
      specVersion = "1.10";
      identifier = { name = "cardano-crypto"; version = "1.1.0"; };
      license = "MIT";
      copyright = "2016-2017 IOHK";
      maintainer = "contact@typed.io";
      author = "Vincent Hanquez";
      homepage = "https://github.com/input-output-hk/cardano-crypto#readme";
      url = "";
      synopsis = "Cryptography primitives for cardano";
      description = "";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.memory)
          (hsPkgs.deepseq)
          (hsPkgs.bytestring)
          (hsPkgs.basement)
          (hsPkgs.foundation)
          (hsPkgs.cryptonite)
          (hsPkgs.cryptonite-openssl)
          (hsPkgs.hashable)
          (hsPkgs.integer-gmp)
          ];
        };
      exes = {
        "golden-tests" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.basement)
            (hsPkgs.foundation)
            (hsPkgs.memory)
            (hsPkgs.bytestring)
            (hsPkgs.cryptonite)
            (hsPkgs.cardano-crypto)
            ] ++ (pkgs.lib).optional (flags.golden-tests-exe) (hsPkgs.inspector);
          };
        };
      tests = {
        "cardano-crypto-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.bytestring)
            (hsPkgs.memory)
            (hsPkgs.cryptonite)
            (hsPkgs.cardano-crypto)
            (hsPkgs.basement)
            (hsPkgs.foundation)
            ];
          };
        "cardano-crypto-golden-tests" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.basement)
            (hsPkgs.foundation)
            (hsPkgs.memory)
            (hsPkgs.bytestring)
            (hsPkgs.cryptonite)
            (hsPkgs.cardano-crypto)
            ] ++ (pkgs.lib).optional (flags.golden-tests) (hsPkgs.inspector);
          };
        };
      benchmarks = {
        "cardano-crypto-bench" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.bytestring)
            (hsPkgs.memory)
            (hsPkgs.cryptonite)
            (hsPkgs.cardano-crypto)
            (hsPkgs.gauge)
            ];
          };
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "https://github.com/input-output-hk/cardano-crypto.git";
      rev = "3c5db489c71a4d70ee43f5f9b979fcde3c797f2a";
      sha256 = "0lss4x41m0ylhximqjc56ps0y3pag3x58wm480pzfa48lpk4gqpk";
      });
    }