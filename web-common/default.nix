{ lib, pkgs, gitignore-nix }:
let
  cleanSrc = gitignore-nix.gitignoreSource ./.;

  replaceName = "sed s/\\$name/$name/g";

  newComponent = pkgs.writeShellScriptBin "new-component" ''
    name=$1
    dir="src/Component/$1"
    file="$dir.purs"
    typesFile="$dir/Types.purs"
    mkdir $dir
    case $2 in
      stateful)
        cat ${./templates/Component/Stateful.purs.template} | ${replaceName} > $modFile
        cat ${./templates/Component/Stateful/Types.purs.template} | ${replaceName} > $typesFile
        ;;
      *)
        cat ${./templates/Component/Stateless.purs.template} | ${replaceName} > $modFile
        cat ${./templates/Component/Stateless/Types.purs.template} | ${replaceName} > $typesFile
        ;;
    esac
  '';
in
{
  inherit cleanSrc newComponent;
}
