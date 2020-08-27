{ plutus ? builtins.fetchTarball {
    name = "plutus";
    url = https://github.com/input-output-hk/plutus/archive/1cd792bd2055510e68572ded07a6c8e24ac0cbb5.tar.gz;
    sha256 = "170w5z1b7q782gwzdvrsmxpswm1q4nf9qj1sif77l9xbj4ai80fl";
  }
}: import (plutus + "/use-case-shell.nix") {}