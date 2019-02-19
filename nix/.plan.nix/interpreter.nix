{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "1.10";
      identifier = { name = "interpreter"; version = "0.1.0.0"; };
      license = "BSD-3-Clause";
      copyright = "2019 IOHK";
      maintainer = "";
      author = "David Smith";
      homepage = "";
      url = "";
      synopsis = "";
      description = "";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.base)
          (hsPkgs.aeson)
          (hsPkgs.bytestring)
          (hsPkgs.exceptions)
          (hsPkgs.file-embed)
          (hsPkgs.transformers)
          (hsPkgs.directory)
          (hsPkgs.bytestring)
          (hsPkgs.http-types)
          (hsPkgs.monad-logger)
          (hsPkgs.filepath)
          (hsPkgs.marlowe)
          (hsPkgs.mtl)
          (hsPkgs.newtype-generics)
          (hsPkgs.servant)
          (hsPkgs.servant-server)
          (hsPkgs.temporary)
          (hsPkgs.time)
          (hsPkgs.wai)
          (hsPkgs.warp)
          (hsPkgs.text)
          (hsPkgs.process)
          ];
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../interpreter; }