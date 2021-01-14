{
  # journalbeat 5.6.0 has a bug so we need to upgrade but its not in stable nixpkgs yet
  journalbeat = self: super: {
    journalbeat = super.journalbeat.overrideDerivation (drv: rec {
      version = "5.6.8";
      name = "journalbeat-${version}";
      src = super.fetchFromGitHub {
        owner = "mheese";
        repo = "journalbeat";
        rev = "v${version}";
        sha256 = "1vgpwnwqjc93nvdpcd52748bwl3r371jb55l17bsgdzrmlcyfm8a";
      };
      GOCACHE = "off";
    });
  };
}
