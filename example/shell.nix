{ plutus ? builtins.fetchTarball {
    name = "plutus";
    url = https://github.com/input-output-hk/plutus/archive/9e8f3a894558ec212dac3d5286f473a2ebd49481.tar.gz;
    sha256 = "0jivkkns58akh8ffrlnn4vmdwrpr7jhd37qax0k2s0yg67s0c4i7";
  }
}: import (plutus + "/use-case-shell.nix") {}
