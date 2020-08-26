{ plutus ? builtins.fetchTarball {
    name = "plutus";
    url = https://github.com/nixos/nixpkgs/archive/d6c1b566b770cf4cf0c6d4a693da6bdf28c2c3b0.tar.gz;
    sha256 = "00vm9shmpywx9dzaj0c7vap1ldimdsr7lw2n8p70qza87nmp9dai";
  }
}: import (plutus + "/use-case-shell.nix") {}