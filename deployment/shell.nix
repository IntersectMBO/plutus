let
  # not in CI so takes forever to build
  #pkgs = (import ../lib.nix {}).pkgs;
  pkgs = import (import ../nix/sources.nix).deployment-nixpkgs {};
in

pkgs.stdenv.mkDerivation rec {
  name = "Plutus-deployments";
  buildInputs = with pkgs; [
    terraform
    awscli
    aws_shell
  ];
  shellHook = ''
    export EDITOR=nvim
    echo "Plutus Deployments" \
    | ${pkgs.figlet}/bin/figlet -f banner -c \
    | ${pkgs.lolcat}/bin/lolcat
        cat <<EOF
   echo preparing terraform
  EOF

  '';
}
