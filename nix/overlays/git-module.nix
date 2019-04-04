{ pkgs, declInput }:

with pkgs.lib;

let
  readRev = let head = builtins.readFile ../../.git/HEAD;
            in
              if hasPrefix "ref: " head
                then builtins.readFile (../../.git + ''/${removeSuffix "\n" (removePrefix "ref: " head)}'')
                else head;
  git-rev = removeSuffix "\n" (if isNull declInput then readRev else declInput.rev);
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