{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "1.10";
      identifier = { name = "meadow"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "";
      author = "Pablo Lamela";
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
          (hsPkgs.aeson-casing)
          (hsPkgs.base)
          (hsPkgs.bytestring)
          (hsPkgs.bytestring)
          (hsPkgs.containers)
          (hsPkgs.cookie)
          (hsPkgs.directory)
          (hsPkgs.exceptions)
          (hsPkgs.file-embed)
          (hsPkgs.filepath)
          (hsPkgs.http-client)
          (hsPkgs.http-client-tls)
          (hsPkgs.http-conduit)
          (hsPkgs.http-types)
          (hsPkgs.interpreter)
          (hsPkgs.jwt)
          (hsPkgs.lens)
          (hsPkgs.marlowe)
          (hsPkgs.monad-logger)
          (hsPkgs.mtl)
          (hsPkgs.newtype-generics)
          (hsPkgs.process)
          (hsPkgs.servant)
          (hsPkgs.servant-client)
          (hsPkgs.servant-client-core)
          (hsPkgs.servant-purescript)
          (hsPkgs.servant-server)
          (hsPkgs.temporary)
          (hsPkgs.text)
          (hsPkgs.time)
          (hsPkgs.time-units)
          (hsPkgs.transformers)
          ];
        };
      exes = {
        "meadow-exe" = {
          depends = [
            (hsPkgs.aeson)
            (hsPkgs.base)
            (hsPkgs.bytestring)
            (hsPkgs.containers)
            (hsPkgs.data-default-class)
            (hsPkgs.directory)
            (hsPkgs.filepath)
            (hsPkgs.http-types)
            (hsPkgs.interpreter)
            (hsPkgs.lens)
            (hsPkgs.meadow)
            (hsPkgs.monad-logger)
            (hsPkgs.mtl)
            (hsPkgs.prometheus)
            (hsPkgs.purescript-bridge)
            (hsPkgs.optparse-applicative)
            (hsPkgs.servant-foreign)
            (hsPkgs.servant-server)
            (hsPkgs.servant-purescript)
            (hsPkgs.text)
            (hsPkgs.wai)
            (hsPkgs.wai-cors)
            (hsPkgs.wai-extra)
            (hsPkgs.warp)
            (hsPkgs.yaml)
            ];
          };
        };
      tests = {
        "meadow-test" = {
          depends = [
            (hsPkgs.base)
            (hsPkgs.bytestring)
            (hsPkgs.hspec)
            (hsPkgs.interpreter)
            (hsPkgs.meadow)
            (hsPkgs.mtl)
            (hsPkgs.raw-strings-qq)
            (hsPkgs.text)
            (hsPkgs.time-units)
            ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././../meadow; }