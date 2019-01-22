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
      rev = "315ccf5d720937c091c8cf3aca8adc8110766a23";
      sha256 = "0c4pi7rlmm3nghkp8h6p33jfvp3j75x512c68xd3ixgj0al1sw0j";
      });
    }