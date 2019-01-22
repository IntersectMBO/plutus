{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = { development = false; };
    package = {
      specVersion = "1.10";
      identifier = { name = "plutus-playground-server"; version = "0.1.0.0"; };
      license = "BSD-3-Clause";
      copyright = "Copyright: (c) 2018 Input Output";
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
          (hsPkgs.base)
          (hsPkgs.bytestring)
          (hsPkgs.containers)
          (hsPkgs.cryptonite)
          (hsPkgs.data-default-class)
          (hsPkgs.directory)
          (hsPkgs.exceptions)
          (hsPkgs.file-embed)
          (hsPkgs.gitrev)
          (hsPkgs.bifunctors)
          (hsPkgs.http-types)
          (hsPkgs.insert-ordered-containers)
          (hsPkgs.lens)
          (hsPkgs.monad-logger)
          (hsPkgs.mtl)
          (hsPkgs.transformers)
          (hsPkgs.newtype-generics)
          (hsPkgs.plutus-playground-lib)
          (hsPkgs.process)
          (hsPkgs.purescript-bridge)
          (hsPkgs.regex-compat)
          (hsPkgs.scientific)
          (hsPkgs.servant)
          (hsPkgs.servant-foreign)
          (hsPkgs.servant-options)
          (hsPkgs.servant-server)
          (hsPkgs.swagger2)
          (hsPkgs.template-haskell)
          (hsPkgs.temporary)
          (hsPkgs.text)
          (hsPkgs.wai)
          (hsPkgs.wai-cors)
          (hsPkgs.wai-extra)
          (hsPkgs.wallet-api)
          (hsPkgs.warp)
          ];
        };
      exes = {
        "plutus-playground-server" = {
          depends = [
            (hsPkgs.aeson)
            (hsPkgs.base)
            (hsPkgs.bytestring)
            (hsPkgs.containers)
            (hsPkgs.cryptonite)
            (hsPkgs.data-default-class)
            (hsPkgs.filepath)
            (hsPkgs.file-embed)
            (hsPkgs.gitrev)
            (hsPkgs.hspec)
            (hsPkgs.http-media)
            (hsPkgs.http-types)
            (hsPkgs.insert-ordered-containers)
            (hsPkgs.lens)
            (hsPkgs.monad-logger)
            (hsPkgs.mtl)
            (hsPkgs.network)
            (hsPkgs.optparse-applicative)
            (hsPkgs.plutus-playground-lib)
            (hsPkgs.plutus-playground-server)
            (hsPkgs.purescript-bridge)
            (hsPkgs.process)
            (hsPkgs.scientific)
            (hsPkgs.servant)
            (hsPkgs.servant-foreign)
            (hsPkgs.servant-options)
            (hsPkgs.servant-purescript)
            (hsPkgs.servant-server)
            (hsPkgs.swagger2)
            (hsPkgs.text)
            (hsPkgs.transformers)
            (hsPkgs.wai)
            (hsPkgs.wai-cors)
            (hsPkgs.wai-extra)
            (hsPkgs.wallet-api)
            (hsPkgs.warp)
            ];
          };
        };
      tests = {
        "plutus-playground-server-test" = {
          depends = [
            (hsPkgs.QuickCheck)
            (hsPkgs.aeson)
            (hsPkgs.base)
            (hsPkgs.bytestring)
            (hsPkgs.containers)
            (hsPkgs.data-default-class)
            (hsPkgs.file-embed)
            (hsPkgs.gitrev)
            (hsPkgs.hspec)
            (hsPkgs.http-media)
            (hsPkgs.http-types)
            (hsPkgs.insert-ordered-containers)
            (hsPkgs.monad-logger)
            (hsPkgs.mtl)
            (hsPkgs.network)
            (hsPkgs.plutus-playground-lib)
            (hsPkgs.plutus-playground-server)
            (hsPkgs.purescript-bridge)
            (hsPkgs.servant)
            (hsPkgs.servant-foreign)
            (hsPkgs.servant-options)
            (hsPkgs.servant-server)
            (hsPkgs.swagger2)
            (hsPkgs.text)
            (hsPkgs.transformers)
            (hsPkgs.unordered-containers)
            (hsPkgs.wai)
            (hsPkgs.wai-cors)
            (hsPkgs.wai-extra)
            (hsPkgs.wallet-api)
            (hsPkgs.warp)
            ];
          build-tools = [ ((hsPkgs.buildPackages).hspec-discover) ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault .././../plutus-playground/plutus-playground-server;
    }