{ pkgs, lib, gitignore-nix, npmlock2nix }:

npmlock2nix.build {
  src = gitignore-nix.gitignoreSource ./.;
  installPhase = "cp -r public $out";
}
