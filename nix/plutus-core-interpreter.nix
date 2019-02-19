{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { eventlog = false; development = false; };
    package = {
      specVersion = "2.0";
      identifier = { name = "plutus-core-interpreter"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "Plutus team";
      author = "Plutus team";
      homepage = "";
      url = "";
      synopsis = "Virtual machine for Plutus Core";
      description = "";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.containers)
          (hsPkgs.mtl)
          (hsPkgs.lens)
          (hsPkgs.language-plutus-core)
          ];
        };
      tests = {
        "plutus-core-interpreter-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.language-plutus-core)
            (hsPkgs.plutus-core-interpreter)
            (hsPkgs.hedgehog)
            (hsPkgs.tasty)
            (hsPkgs.tasty-hunit)
            (hsPkgs.tasty-hedgehog)
            (hsPkgs.mtl)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././plutus-core-interpreter; }