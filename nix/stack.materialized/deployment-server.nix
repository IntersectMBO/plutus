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
      specVersion = "2.0";
      identifier = { name = "deployment-server"; version = "0.1.0.0"; };
      license = "Apache-2.0";
      copyright = "";
      maintainer = "david.smith@tweag.io";
      author = "David Smith";
      homepage = "";
      url = "";
      synopsis = "";
      description = "Continuous Delivery server for Plutus Playgrounds";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [ "README.md" ];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (buildDepError "base"))
          (hsPkgs."aeson" or (buildDepError "aeson"))
          (hsPkgs."bytestring" or (buildDepError "bytestring"))
          (hsPkgs."directory" or (buildDepError "directory"))
          (hsPkgs."github" or (buildDepError "github"))
          (hsPkgs."github-webhooks" or (buildDepError "github-webhooks"))
          (hsPkgs."mtl" or (buildDepError "mtl"))
          (hsPkgs."newtype-generics" or (buildDepError "newtype-generics"))
          (hsPkgs."optparse-generic" or (buildDepError "optparse-generic"))
          (hsPkgs."servant" or (buildDepError "servant"))
          (hsPkgs."servant-github-webhook" or (buildDepError "servant-github-webhook"))
          (hsPkgs."servant-server" or (buildDepError "servant-server"))
          (hsPkgs."temporary" or (buildDepError "temporary"))
          (hsPkgs."typed-process" or (buildDepError "typed-process"))
          (hsPkgs."text" or (buildDepError "text"))
          (hsPkgs."wai" or (buildDepError "wai"))
          ];
        buildable = true;
        modules = [ "Deploy/Server" "Deploy/Types" "Deploy/Worker" ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "deployment-server-exe" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."aeson" or (buildDepError "aeson"))
            (hsPkgs."bytestring" or (buildDepError "bytestring"))
            (hsPkgs."containers" or (buildDepError "containers"))
            (hsPkgs."deployment-server" or (buildDepError "deployment-server"))
            (hsPkgs."newtype-generics" or (buildDepError "newtype-generics"))
            (hsPkgs."optparse-generic" or (buildDepError "optparse-generic"))
            (hsPkgs."servant-github-webhook" or (buildDepError "servant-github-webhook"))
            (hsPkgs."text" or (buildDepError "text"))
            (hsPkgs."warp" or (buildDepError "warp"))
            ];
          buildable = true;
          modules = [ "Paths_deployment_server" ];
          hsSourceDirs = [ "app" ];
          mainPath = [ "Main.hs" ];
          };
        };
      tests = {
        "deployment-server-test" = {
          depends = [
            (hsPkgs."base" or (buildDepError "base"))
            (hsPkgs."deployment-server" or (buildDepError "deployment-server"))
            ];
          buildable = true;
          modules = [ "Paths_deployment_server" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./deployment-server;
    }