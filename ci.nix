let main = import default.nix;
in { 
  inherit (main.pkgs) git;
}
