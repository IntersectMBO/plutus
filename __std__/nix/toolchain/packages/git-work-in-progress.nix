{ inputs, cell }:

# TODO(std) remove the --no-verify after adding the pre-commit
inputs.nixpkgs.writeShellApplication {
  name = "wip";
  text = "git add . && git commit -m WIP --no-verify";
  runtimeInputs = [ inputs.nixpkgs.git ];
}
