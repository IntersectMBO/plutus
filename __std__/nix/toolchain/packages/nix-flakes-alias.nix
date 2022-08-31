{ inputs, cell }:

# TODO(std) what is this for?
inputs.nixpkgs.runCommand "nix-flakes-alias" { } ''
  mkdir -p $out/bin
  ln -sv ${inputs.nixpkgs.nixFlakes}/bin/nix $out/bin/nix-flakes
''
