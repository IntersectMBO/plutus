{ inputs, cell }:

inputs.nixpkgs.writeShellApplication {
  name = "irrelevant";
  text = ''
    my_list=(
      item_1
      item_2
    )
    if [[ "${my_list[*]}" =~ "item_3" ]]; then 
      echo inside_list
    else 
      echo outside_list
    fi 
  '';
}




# { inputs, cell }:

# # TODO(std) needs to be fixed once __std__ is brought to the toplevel.
# # TODO(std) remove derivations from the broken list as they get fixed
# inputs.nixpkgs.writeShellApplication {
#   name = "check-the-flake";
#   runtimeInputs = [ inputs.nixpkgs.nix ];
#   text = ''
#     root="$(repo-root)"

#     shell_fragments=$(
#       find \
#         "$root/__std__/nix" \
#         -name "*.nix" \
#         -and -not -name "*default.nix" \
#         -and -path "*devshells*" \
#         -exec basename {} .nix \;
#     )

#     for fragment in $shell_fragments; do 
#       echo building "$fragment" 
#       nix develop ".#$fragment" --build
#     done 

#     derivation_fragments=$(
#       find \
#         "$(repo-root)/__std__/nix" \
#         -name "*.nix" \
#         -and -not -name "*default.nix" \
#         -and -not -path "*library*" \
#         -and -not -path "*devshells*" \
#         -exec basename {} .nix \;
#     ) 

#     # shellcheck disable=SC2034
#     broken_fragments=(
#       system-f-in-agda-paper
#       unraveling-recursion-paper
#     )

#     for fragment in $derivation_fragments; do 
#       # shellcheck disable=SC2076
#       # shellcheck disable=SC2034
#       if [[ "${{broken_fragments[*]}" =~ "$fragment" ]]; then 
#         echo building "$fragment" 
#         nix build ".#$fragment"
#       else 
#         echo skipping broken "$fragment"
#       fi 
#     done 
#   '';
# }
