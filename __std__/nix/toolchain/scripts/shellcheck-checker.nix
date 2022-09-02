{ inputs, cell }:

let
  src = inputs.nixpkgs.lib.sourceFilesBySuffices
    (cell.library.gitignore-nix.gitignoreSource inputs.self)
    [ ".sh" ];
in

inputs.nixpkgs.runCommand "shellcheck-checker"
{
  buildInputs = [ inputs.nixpkgs.shellcheck ];
}
  ''
    EXIT_STATUS=0
    cd ${src}
    while IFS= read -r -d ''' i
    do
      if shellcheck -x -e 1008 -e 2148 "$i"
      then
        echo "$i [ PASSED ]"
      else
        echo "$i [ FAILED ]"
        EXIT_STATUS=$(($EXIT_STATUS+1))
      fi
    done <  <(find -name '*.sh' -print0)
    echo $EXIT_STATUS > $out
    echo Total Failed Files: $EXIT_STATUS
    exit "$EXIT_STATUS"
  ''
