let
  buildDepError = pkg:
    builtins.throw ''
      The Haskell package set does not contain the package: ${pkg} (build dependency).
      
      If you are using Stackage, make sure that you are using a snapshot that contains the package. Otherwise you may need to update the Hackage snapshot you are using, usually by updating haskell.nix.
      '';
  sysDepError = pkg:
    builtins.throw ''
      The Nixpkgs package set does not contain the package: ${pkg} (system dependency).
      
      You may need to augment the system package mapping in haskell.nix so that it can be found.
      '';
  pkgConfDepError = pkg:
    builtins.throw ''
      The pkg-conf packages does not contain the package: ${pkg} (pkg-conf dependency).
      
      You may need to augment the pkg-conf package mapping in haskell.nix so that it can be found.
      '';
  exeDepError = pkg:
    builtins.throw ''
      The local executable components do not include the component: ${pkg} (executable dependency).
      '';
  legacyExeDepError = pkg:
    builtins.throw ''
      The Haskell package set does not contain the package: ${pkg} (executable dependency).
      
      If you are using Stackage, make sure that you are using a snapshot that contains the package. Otherwise you may need to update the Hackage snapshot you are using, usually by updating haskell.nix.
      '';
  buildToolDepError = pkg:
    builtins.throw ''
      Neither the Haskell package set or the Nixpkgs package set contain the package: ${pkg} (build tool dependency).
      
      If this is a system dependency:
      You may need to augment the system package mapping in haskell.nix so that it can be found.
      
      If this is a Haskell dependency:
      If you are using Stackage, make sure that you are using a snapshot that contains the package. Otherwise you may need to update the Hackage snapshot you are using, usually by updating haskell.nix.
      '';
in { system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "1.10";
      identifier = { name = "marlowe-playground-server"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "";
      author = "Pablo Lamela";
      homepage = "";
      url = "";
      synopsis = "";
      description = "";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" "NOTICE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [ "README.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."aeson" or (buildDepError "aeson"))
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."containers" or (buildDepError "containers"))
          (hsPkgs."cookie" or (buildDepError "cookie"))
          (hsPkgs."directory" or (buildDepError "directory"))
          (hsPkgs."exceptions" or (buildDepError "exceptions"))
          (hsPkgs."file-embed" or (buildDepError "file-embed"))
          (hsPkgs."filepath" or (buildDepError "filepath"))
          (hsPkgs."http-client" or (buildDepError "http-client"))
          (hsPkgs."http-client-tls" or (buildDepError "http-client-tls"))
          (hsPkgs."http-conduit" or (buildDepError "http-conduit"))
          (hsPkgs."http-types" or (buildDepError "http-types"))
          (hsPkgs."playground-common" or (buildDepError "playground-common"))
          (hsPkgs."jwt" or (buildDepError "jwt"))
          (hsPkgs."lens" or (buildDepError "lens"))
          (hsPkgs."marlowe" or (buildDepError "marlowe"))
          (hsPkgs."marlowe-symbolic" or (buildDepError "marlowe-symbolic"))
          (hsPkgs."monad-logger" or (buildDepError "monad-logger"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."newtype-generics" or (buildDepError "newtype-generics"))
          (hsPkgs."process" or (buildDepError "process"))
          (hsPkgs."servant" or (buildDepError "servant"))
          (hsPkgs."servant-client" or (buildDepError "servant-client"))
          (hsPkgs."servant-client-core" or (buildDepError "servant-client-core"))
          (hsPkgs."servant-purescript" or (buildDepError "servant-purescript"))
          (hsPkgs."servant-server" or (buildDepError "servant-server"))
          (hsPkgs."servant-websockets" or (buildDepError "servant-websockets"))
          (hsPkgs."stm" or (buildDepError "stm"))
          (hsPkgs."temporary" or (buildDepError "temporary"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."time" or (buildDepError "time"))
          (hsPkgs."time-units" or (buildDepError "time-units"))
          (hsPkgs."transformers" or (buildDepError "transformers"))
          (hsPkgs."uuid" or (buildDepError "uuid"))
          (hsPkgs."websockets" or (buildDepError "websockets"))
          ];
        buildable = true;
        modules = [
          "Server"
          "API"
          "Interpreter"
          "WebSocket"
          "Marlowe/Contracts"
          "Marlowe/Config"
          ];
        hsSourceDirs = [ "src" "contracts" ];
        };
      exes = {
        "marlowe-playground-server" = {
          depends = [
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."data-default-class" or (buildDepError "data-default-class"))
            (hsPkgs."directory" or (buildDepError "directory"))
            (hsPkgs."filepath" or (buildDepError "filepath"))
            (hsPkgs."http-client" or (buildDepError "http-client"))
            (hsPkgs."http-client-tls" or (buildDepError "http-client-tls"))
            (hsPkgs."http-types" or (buildDepError "http-types"))
            (hsPkgs."playground-common" or (buildDepError "playground-common"))
            (hsPkgs."lens" or (buildDepError "lens"))
            (hsPkgs."marlowe" or (buildDepError "marlowe"))
            (hsPkgs."marlowe-playground-server" or (buildDepError "marlowe-playground-server"))
            (hsPkgs."marlowe-symbolic" or (buildDepError "marlowe-symbolic"))
            (hsPkgs."monad-logger" or (buildDepError "monad-logger"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."plutus-ledger" or (buildDepError "plutus-ledger"))
            (hsPkgs."prometheus" or (buildDepError "prometheus"))
            (hsPkgs."purescript-bridge" or (buildDepError "purescript-bridge"))
            (hsPkgs."optparse-applicative" or (buildDepError "optparse-applicative"))
            (hsPkgs."servant-client" or (buildDepError "servant-client"))
            (hsPkgs."servant-foreign" or (buildDepError "servant-foreign"))
            (hsPkgs."servant-server" or (buildDepError "servant-server"))
            (hsPkgs."servant-purescript" or (buildDepError "servant-purescript"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."wai" or (buildDepError "wai"))
            (hsPkgs."wai-cors" or (buildDepError "wai-cors"))
            (hsPkgs."wai-extra" or (buildDepError "wai-extra"))
            (hsPkgs."warp" or (buildDepError "warp"))
            (hsPkgs."yaml" or (buildDepError "yaml"))
            ];
          buildable = true;
          modules = [
            "Webserver"
            "PSGenerator"
            "Types"
            "Escrow"
            "CouponBondGuaranteed"
            "ZeroCouponBond"
            "Swap"
            ];
          hsSourceDirs = [ "app" "contracts" ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "marlowe-playground-server-test" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."hspec" or (buildDepError "hspec"))
            (hsPkgs."playground-common" or (buildDepError "playground-common"))
            (hsPkgs."marlowe-playground-server" or (buildDepError "marlowe-playground-server"))
            (hsPkgs."mtl" or (buildDepError "mtl"))
            (hsPkgs."raw-strings-qq" or (buildDepError "raw-strings-qq"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."time-units" or (buildDepError "time-units"))
            ];
          buildable = true;
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./marlowe-playground-server;
    }