{ system
  , compiler
  , flags
  , pkgs
  , hsPkgs
  , pkgconfPkgs
  , errorHandler
  , config
  , ... }:
  {
    flags = { openssl = false; };
    package = {
      specVersion = "1.10";
      identifier = { name = "github"; version = "0.22"; };
      license = "BSD-3-Clause";
      copyright = "Copyright 2012-2013 Mike Burns, Copyright 2013-2015 John Wiegley, Copyright 2016-2019 Oleg Grenrus";
      maintainer = "Oleg Grenrus <oleg.grenrus@iki.fi>";
      author = "Mike Burns, John Wiegley, Oleg Grenrus";
      homepage = "https://github.com/phadej/github";
      url = "";
      synopsis = "Access to the GitHub API, v3.";
      description = "The GitHub API provides programmatic access to the full\nGitHub Web site, from Issues to Gists to repos down to the underlying git data\nlike references and trees. This library wraps all of that, exposing a basic but\nHaskell-friendly set of functions and data structures.\n\nFor supported endpoints see \"GitHub\" module.\n\n> import qualified GitHub as GH\n>\n> main :: IO ()\n> main = do\n>     possibleUser <- GH.executeRequest' \$ GH.userInfoForR \"phadej\"\n>     print possibleUser\n\nFor more of an overview please see the README: <https://github.com/phadej/github/blob/master/README.md>";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = "";
      dataFiles = [];
      extraSrcFiles = [
        "README.md"
        "CHANGELOG.md"
        "fixtures/issue-search.json"
        "fixtures/list-teams.json"
        "fixtures/members-list.json"
        "fixtures/pull-request-opened.json"
        "fixtures/pull-request-review-requested.json"
        "fixtures/user-organizations.json"
        "fixtures/user.json"
        ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = ([
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."binary" or (errorHandler.buildDepError "binary"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."base-compat" or (errorHandler.buildDepError "base-compat"))
          (hsPkgs."base16-bytestring" or (errorHandler.buildDepError "base16-bytestring"))
          (hsPkgs."binary-instances" or (errorHandler.buildDepError "binary-instances"))
          (hsPkgs."cryptohash-sha1" or (errorHandler.buildDepError "cryptohash-sha1"))
          (hsPkgs."deepseq-generics" or (errorHandler.buildDepError "deepseq-generics"))
          (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
          (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
          (hsPkgs."http-client" or (errorHandler.buildDepError "http-client"))
          (hsPkgs."http-link-header" or (errorHandler.buildDepError "http-link-header"))
          (hsPkgs."http-types" or (errorHandler.buildDepError "http-types"))
          (hsPkgs."iso8601-time" or (errorHandler.buildDepError "iso8601-time"))
          (hsPkgs."network-uri" or (errorHandler.buildDepError "network-uri"))
          (hsPkgs."tagged" or (errorHandler.buildDepError "tagged"))
          (hsPkgs."transformers-compat" or (errorHandler.buildDepError "transformers-compat"))
          (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
          (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
          (hsPkgs."vector-instances" or (errorHandler.buildDepError "vector-instances"))
          ] ++ (if flags.openssl
          then [
            (hsPkgs."http-client-openssl" or (errorHandler.buildDepError "http-client-openssl"))
            (hsPkgs."HsOpenSSL" or (errorHandler.buildDepError "HsOpenSSL"))
            (hsPkgs."HsOpenSSL-x509-system" or (errorHandler.buildDepError "HsOpenSSL-x509-system"))
            ]
          else [
            (hsPkgs."http-client-tls" or (errorHandler.buildDepError "http-client-tls"))
            (hsPkgs."tls" or (errorHandler.buildDepError "tls"))
            ])) ++ (pkgs.lib).optional (!(compiler.isGhc && (compiler.version).ge "8.0")) (hsPkgs."semigroups" or (errorHandler.buildDepError "semigroups"));
        buildable = true;
        modules = [
          "GitHub"
          "GitHub/Auth"
          "GitHub/Data"
          "GitHub/Data/Activities"
          "GitHub/Data/Comments"
          "GitHub/Data/Content"
          "GitHub/Data/Definitions"
          "GitHub/Data/DeployKeys"
          "GitHub/Data/Deployments"
          "GitHub/Data/Email"
          "GitHub/Data/Events"
          "GitHub/Data/Gists"
          "GitHub/Data/GitData"
          "GitHub/Data/Id"
          "GitHub/Data/Invitation"
          "GitHub/Data/Issues"
          "GitHub/Data/Milestone"
          "GitHub/Data/Name"
          "GitHub/Data/Options"
          "GitHub/Data/PublicSSHKeys"
          "GitHub/Data/PullRequests"
          "GitHub/Data/RateLimit"
          "GitHub/Data/Releases"
          "GitHub/Data/Repos"
          "GitHub/Data/Request"
          "GitHub/Data/Reviews"
          "GitHub/Data/Search"
          "GitHub/Data/Statuses"
          "GitHub/Data/Teams"
          "GitHub/Data/URL"
          "GitHub/Data/Webhooks"
          "GitHub/Data/Webhooks/Validate"
          "GitHub/Endpoints/Activity/Events"
          "GitHub/Endpoints/Activity/Starring"
          "GitHub/Endpoints/Activity/Notifications"
          "GitHub/Endpoints/Activity/Watching"
          "GitHub/Endpoints/Gists"
          "GitHub/Endpoints/Gists/Comments"
          "GitHub/Endpoints/GitData/Blobs"
          "GitHub/Endpoints/GitData/Commits"
          "GitHub/Endpoints/GitData/References"
          "GitHub/Endpoints/GitData/Trees"
          "GitHub/Endpoints/Issues"
          "GitHub/Endpoints/Issues/Comments"
          "GitHub/Endpoints/Issues/Events"
          "GitHub/Endpoints/Issues/Labels"
          "GitHub/Endpoints/Issues/Milestones"
          "GitHub/Endpoints/Organizations"
          "GitHub/Endpoints/Organizations/Members"
          "GitHub/Endpoints/Organizations/Teams"
          "GitHub/Endpoints/PullRequests"
          "GitHub/Endpoints/PullRequests/Comments"
          "GitHub/Endpoints/PullRequests/Reviews"
          "GitHub/Endpoints/RateLimit"
          "GitHub/Endpoints/Repos"
          "GitHub/Endpoints/Repos/Collaborators"
          "GitHub/Endpoints/Repos/Comments"
          "GitHub/Endpoints/Repos/Commits"
          "GitHub/Endpoints/Repos/Contents"
          "GitHub/Endpoints/Repos/DeployKeys"
          "GitHub/Endpoints/Repos/Deployments"
          "GitHub/Endpoints/Repos/Forks"
          "GitHub/Endpoints/Repos/Releases"
          "GitHub/Endpoints/Repos/Statuses"
          "GitHub/Endpoints/Repos/Webhooks"
          "GitHub/Endpoints/Repos/Invitations"
          "GitHub/Endpoints/Search"
          "GitHub/Endpoints/Users"
          "GitHub/Endpoints/Users/Emails"
          "GitHub/Endpoints/Users/Followers"
          "GitHub/Endpoints/Users/PublicSSHKeys"
          "GitHub/Internal/Prelude"
          "GitHub/Request"
          ];
        hsSourceDirs = [ "src" ];
        };
      tests = {
        "github-test" = {
          depends = [
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."base-compat" or (errorHandler.buildDepError "base-compat"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."file-embed" or (errorHandler.buildDepError "file-embed"))
            (hsPkgs."github" or (errorHandler.buildDepError "github"))
            (hsPkgs."tagged" or (errorHandler.buildDepError "tagged"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."hspec" or (errorHandler.buildDepError "hspec"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.hspec-discover or (pkgs.buildPackages.hspec-discover or (errorHandler.buildToolDepError "hspec-discover")))
            ];
          buildable = true;
          modules = [
            "GitHub/ActivitySpec"
            "GitHub/CommitsSpec"
            "GitHub/EventsSpec"
            "GitHub/IssuesSpec"
            "GitHub/OrganizationsSpec"
            "GitHub/PullRequestReviewsSpec"
            "GitHub/PublicSSHKeysSpec"
            "GitHub/PullRequestsSpec"
            "GitHub/RateLimitSpec"
            "GitHub/ReleasesSpec"
            "GitHub/ReposSpec"
            "GitHub/SearchSpec"
            "GitHub/UsersSpec"
            ];
          hsSourceDirs = [ "spec" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault .././.source-repository-packages/4; }