{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "2.0";
      identifier = { name = "plutus-playground-server"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "kris.jenkins@tweag.io";
      author = "Kris Jenkins";
      homepage = "https://github.com/iohk/plutus#readme";
      url = "";
      synopsis = "";
      description = "Please see the README on GitHub at <https://github.com/input-output-hk/plutus#readme>";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs.aeson)
          (hsPkgs.aeson-casing)
          (hsPkgs.base)
          (hsPkgs.bytestring)
          (hsPkgs.containers)
          (hsPkgs.cookie)
          (hsPkgs.directory)
          (hsPkgs.exceptions)
          (hsPkgs.file-embed)
          (hsPkgs.http-conduit)
          (hsPkgs.http-client-tls)
          (hsPkgs.http-client)
          (hsPkgs.http-types)
          (hsPkgs.interpreter)
          (hsPkgs.jwt)
          (hsPkgs.lens)
          (hsPkgs.monad-logger)
          (hsPkgs.mtl)
          (hsPkgs.transformers)
          (hsPkgs.newtype-generics)
          (hsPkgs.plutus-playground-lib)
          (hsPkgs.process)
          (hsPkgs.regex-compat)
          (hsPkgs.servant)
          (hsPkgs.servant-purescript)
          (hsPkgs.servant-client)
          (hsPkgs.servant-client-core)
          (hsPkgs.servant-ekg)
          (hsPkgs.servant-server)
          (hsPkgs.swagger2)
          (hsPkgs.temporary)
          (hsPkgs.text)
          (hsPkgs.time)
          (hsPkgs.wallet-api)
          ];
        };
      exes = {
        "plutus-playground-server" = {
          depends = [
            (hsPkgs.aeson)
            (hsPkgs.base)
            (hsPkgs.bytestring)
            (hsPkgs.containers)
            (hsPkgs.data-default-class)
            (hsPkgs.ekg)
            (hsPkgs.ekg-core)
            (hsPkgs.ekg-statsd)
            (hsPkgs.filepath)
            (hsPkgs.gitrev)
            (hsPkgs.http-types)
            (hsPkgs.interpreter)
            (hsPkgs.lens)
            (hsPkgs.monad-logger)
            (hsPkgs.mtl)
            (hsPkgs.optparse-applicative)
            (hsPkgs.plutus-playground-lib)
            (hsPkgs.plutus-playground-server)
            (hsPkgs.purescript-bridge)
            (hsPkgs.servant)
            (hsPkgs.servant-ekg)
            (hsPkgs.servant-foreign)
            (hsPkgs.servant-purescript)
            (hsPkgs.servant-server)
            (hsPkgs.text)
            (hsPkgs.transformers)
            (hsPkgs.wai)
            (hsPkgs.wai-cors)
            (hsPkgs.wai-extra)
            (hsPkgs.wallet-api)
            (hsPkgs.warp)
            (hsPkgs.yaml)
            ];
          };
        };
      tests = {
        "plutus-playground-server-test" = {
          depends = [
            (hsPkgs.aeson)
            (hsPkgs.base)
            (hsPkgs.bytestring)
            (hsPkgs.hspec)
            (hsPkgs.insert-ordered-containers)
            (hsPkgs.interpreter)
            (hsPkgs.mtl)
            (hsPkgs.plutus-playground-lib)
            (hsPkgs.plutus-playground-server)
            (hsPkgs.swagger2)
            (hsPkgs.text)
            (hsPkgs.transformers)
            (hsPkgs.wallet-api)
            ];
          build-tools = [ ((hsPkgs.buildPackages).hspec-discover) ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././plutus-playground-server; }