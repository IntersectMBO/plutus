let
  # not in CI so takes forever to build
  #pkgs = (import ../lib.nix {}).pkgs;
  iohkNix = (import ../lib.nix {}).iohkNix;
  pkgs = import (iohkNix.fetchNixpkgs ./nixpkgs-src.json) {};
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
