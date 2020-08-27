{ plutus ? builtins.fetchTarball {
    name = "plutus";
    url = https://github.com/input-output-hk/plutus/archive/c586f76c926b03f9b374ce4c17b81ed4486eccf2.tar.gz;
    sha256 = "175bzm4crinrhszh9mc247l0dnwlb2g20xjy7j91g4rl15pdvirn";
  }
}: import (plutus + "/use-case-shell.nix") {}