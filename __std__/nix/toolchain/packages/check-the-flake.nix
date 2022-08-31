{ inputs, cell }:

# TODO(std) needs to be fixed once __std__ is brought to the toplevel.
# TODO(std) remove broken_fragments as they get fixed
inputs.nixpkgs.writeShellApplication {
  name = "check-the-flake";
  runtimeInputs = [ inputs.nixpkgs.nix ];
  text = ''
    root="$(repo-root)"

    shell_fragments=$(
      find \
        "$root/__std__/nix" \
        -name "*.nix" \
        -and -not -name "*default.nix" \
        -and -path "*devshells*" \
        -exec basename {} .nix \;
    )

    for fragment in $shell_fragments; do 
      echo building "$fragment" 
      nix develop ".#$fragment" --build
    done 

    derivation_fragments=$(
      find \
        "$(repo-root)/__std__/nix" \
        -name "*.nix" \
        -and -not -name "*default.nix" \
        -and -not -path "*library*" \
        -and -not -path "*devshells*" \
        -and -not -path "*devshellProfiles*" \
        -exec basename {} .nix \;
    ) 

    for fragment in $derivation_fragments; do 
      echo building "$fragment" 
      nix build ".#$fragment"
    done 
  '';
}
