{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "2.0";
      identifier = { name = "plutus-exe"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "michael.peyton-jones@iohk.io";
      author = "Michael Peyton jones";
      homepage = "";
      url = "";
      synopsis = "Executable for Plutus Core tools.";
      description = "This provides an executable which handles typechecking and evaluation of Plutus Core programs on the command line.";
      buildType = "Simple";
      };
    components = {
      exes = {
        "plc" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.language-plutus-core)
            (hsPkgs.plutus-core-interpreter)
            (hsPkgs.transformers)
            (hsPkgs.bytestring)
            (hsPkgs.text)
            (hsPkgs.lens)
            (hsPkgs.prettyprinter)
            (hsPkgs.optparse-applicative)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../plutus-exe; }