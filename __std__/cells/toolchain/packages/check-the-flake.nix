{ inputs, cell }:

# TODO(std) path must be fixed once __std__ is brought to the toplevel.
# TODO(std) make this part of CI
# TODO(std) turn this into a single derivation using recurseForDerivations
cell.library.pkgs.writeShellApplication {
  name = "check-the-flake";
  runtimeInputs = [
    cell.library.pkgs.nix
    cell.packages.repo-root
  ];
  text = ''
    set +e

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
        -and -not -path "*automation*" \
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
