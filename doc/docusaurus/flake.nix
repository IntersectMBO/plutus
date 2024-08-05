{
  description = "A flake for developing the docusaurus site";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "x86_64-darwin" "aarch64-darwin" "aarch64-linux" ];
      perSystem = { pkgs, ... }: {
        devShells.default = pkgs.mkShell {
          packages = [ pkgs.yarn pkgs.linkchecker ];
          shellHook = ''
            PS1="\[\033[32m\]\u@\h\[\033[0m\]:\[\033[33m\]\w\[\033[0m\]\$ "
          '';
        };
      };
    };
}
