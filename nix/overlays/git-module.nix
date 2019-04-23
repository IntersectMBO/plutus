{ pkgs, git-rev }:

with pkgs.lib;

# This overlay will alter the Git.hs haskell module with the current git revision. If declInput.rev
# is avilable the it will use that (Hydra) otherwise it will look in the .git directory (local builds)
let
  gitModulePatch = pkgs.writeText "gitModulePatch" ''
    diff --git a/src/Git.hs b/src/Git.hs
    index b0398a7..45a9066 100644
    --- a/src/Git.hs
    +++ b/src/Git.hs
    @@ -1,4 +1,4 @@
     module Git where
    
     gitHead :: String
    -gitHead = "master"
    +gitHead = "${git-rev}"
  '';
in
self: super: {
    plutus-playground-server = super.plutus-playground-server.overrideDerivation (oldAttrs: {
      patches = [gitModulePatch];
    });
    meadow = super.meadow.overrideDerivation (oldAttrs: {
      patches = [gitModulePatch];
    });
}
