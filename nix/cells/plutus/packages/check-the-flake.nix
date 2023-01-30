{ inputs, cell }:

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
        "$root/nix/cells" \
        -name "*.nix" \
        -and -not -name "*default.nix" \
        -and -path "*/devshells*" \
        -exec basename {} .nix \;
    )

    for fragment in $shell_fragments; do
      echo building "$fragment"
      GC_DONT_GC=1 nix develop ".#$fragment" --build --no-warn-dirty --accept-flake-config
    done

    derivation_fragments=$(
      find \
        "$root/nix/cells" \
        -name "*.nix" \
        -and -not -name "*default.nix" \
        -and -path "*/packages*" \
        -exec basename {} .nix \;
    )

    for fragment in $derivation_fragments; do
      echo building "$fragment"
      GC_DONT_GC=1 nix build ".#$fragment" --no-warn-dirty --accept-flake-config
    done
  '';
}
