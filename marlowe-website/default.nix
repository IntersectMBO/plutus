{ pkgs, lib, gitignore-nix, npmlock2nix }:

npmlock2nix.build {
  src = gitignore-nix.gitignoreSource ./.;
  installPhase = "cp -r public $out";
  node_modules_mode = "copy";

  node_modules_attrs = {
    packageLockJson = ./package-lock.json;
    packageJson = ./package.json;
  };
}
