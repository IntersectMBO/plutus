{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "2.0";
      identifier = { name = "interpreter"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
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
          (hsPkgs.aeson)
          (hsPkgs.base)
          (hsPkgs.bytestring)
          (hsPkgs.bytestring)
          (hsPkgs.cookie)
          (hsPkgs.directory)
          (hsPkgs.exceptions)
          (hsPkgs.filepath)
          (hsPkgs.hashable)
          (hsPkgs.http-types)
          (hsPkgs.monad-logger)
          (hsPkgs.mtl)
          (hsPkgs.newtype-generics)
          (hsPkgs.process)
          (hsPkgs.prometheus)
          (hsPkgs.servant)
          (hsPkgs.servant-purescript)
          (hsPkgs.servant-server)
          (hsPkgs.temporary)
          (hsPkgs.text)
          (hsPkgs.time)
          (hsPkgs.time-out)
          (hsPkgs.time-units)
          (hsPkgs.transformers)
          (hsPkgs.unordered-containers)
          (hsPkgs.wai)
          ];
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../interpreter; }