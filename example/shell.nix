{ plutus ? builtins.fetchTarball {
    name = "plutus";
    url = https://github.com/input-output-hk/plutus/archive/0c29874ebc27d73f39384945bc38d15e5f4ead7d.tar.gz;
    sha256 = "03d1iqaxvm3jq273bc3kh3c3rv1gj5rpm0plxxj6rrfxzad80vza";
  }
}: import (plutus + "/use-case-shell.nix") {}
