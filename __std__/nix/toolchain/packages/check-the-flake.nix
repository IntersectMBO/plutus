{ inputs, cell }:

# TODO(std) needs to be fixed once __std__ is brought to the toplevel.
inputs.nixpkgs.writeShellApplication {
  name = "check-the-flake";
  runtimeInputs = [ inputs.nixpkgs.nix ];
  text = ''
    root="$(repo-root)"

    shell_files=$(
      find \
        "$root/__std__/nix" \
        -name "*.nix" \
        -and -not -name "*default.nix" \
        -and -path "*devshells*"
    ) 

    for file in "$shell_files"; do 
      nix develop ".#$file" --build
    done 

    derivation_files=$(
      find \
        "$(repo-root)/__std__/nix" \
        -name "*.nix" \
        -and -not -name "*default.nix" \
        -and -not -path "*library*" \
        -and -not -path "*devshells*"
    ) 

    for file in "$derivation_files"; do 
      nix build ".#$file"
    done 
  '';
}

