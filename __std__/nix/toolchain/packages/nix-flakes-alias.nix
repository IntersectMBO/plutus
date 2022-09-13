{ inputs, cell }:

# TODO(std) remove this when everything else is done
inputs.nixpkgs.runCommand "nix-flakes-alias" { } ''
  mkdir -p $out/bin
  ln -sv ${inputs.nixpkgs.nixFlakes}/bin/nix $out/bin/nix-flakes
''
