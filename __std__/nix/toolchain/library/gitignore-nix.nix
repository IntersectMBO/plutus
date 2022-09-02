{ inputs, cell }:

# TODO(std) can we fetch this directly from github instead of using the flake?
inputs.nixpkgs.callPackage inputs.gitignore-nix {}
