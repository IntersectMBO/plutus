{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "1.10";
      identifier = { name = "servant-purescript"; version = "0.9.0.2"; };
      license = "BSD-3-Clause";
      copyright = "Copyright: (c) 2016 Robert Klotzner";
      maintainer = "robert Dot klotzner A T gmx Dot at";
      author = "Robert Klotzner";
      homepage = "https://github.com/eskimor/servant-purescript#readme";
      url = "";
      synopsis = "Generate PureScript accessor functions for you servant API";
      description = "Please see README.md";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.aeson)
          (hsPkgs.bytestring)
          (hsPkgs.containers)
          (hsPkgs.directory)
          (hsPkgs.filepath)
          (hsPkgs.http-types)
          (hsPkgs.lens)
          (hsPkgs.mainland-pretty)
          (hsPkgs.purescript-bridge)
          (hsPkgs.servant)
          (hsPkgs.servant-foreign)
          (hsPkgs.servant-server)
          (hsPkgs.servant-subscriber)
          (hsPkgs.text)
          ];
        };
      tests = {
        "servant-purescript-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.aeson)
            (hsPkgs.containers)
            (hsPkgs.mainland-pretty)
            (hsPkgs.lens)
            (hsPkgs.purescript-bridge)
            (hsPkgs.servant)
            (hsPkgs.servant-foreign)
            (hsPkgs.servant-purescript)
            (hsPkgs.servant-subscriber)
            (hsPkgs.text)
            ];
          };
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "https://github.com/shmish111/servant-purescript.git";
      rev = "18e1b61bf0aa3792285c6d8ecd0e4a72d76e34f5";
      sha256 = "1c35c49f12mw6f0h6njsk42nbgmggb0kbr05iyz8gcy407y4jw9r";
      });
    }