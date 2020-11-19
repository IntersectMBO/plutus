let
  # not in CI so takes forever to build
  pkgs = (import ../lib.nix { }).pkgs;
in
pkgs.stdenv.mkDerivation rec {
  name = "Plutus-deployments";
  buildInputs = with pkgs; [
    terraform
    awscli
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
