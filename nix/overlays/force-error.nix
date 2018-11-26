{ pkgs, filter }:

with pkgs.lib;

self: super: {
  mkDerivation = args: super.mkDerivation (args // optionalAttrs (filter args.pname) {
    configureFlags = (args.configureFlags or []) ++ [ "--ghc-option=-Werror" ];
  });
}
