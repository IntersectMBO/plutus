# This file evaluates to a derivation that builds the docusaurus site.
{ repoRoot, inputs, pkgs, system, lib }:

let

  node-modules = pkgs.mkYarnPackage {
    name = "node-modules";
    src = ../doc/docusaurus;
  };

  docusaurus-site = pkgs.stdenv.mkDerivation {
    name = "docusaurus-site";
    src = ../doc/docusaurus;
    buildInputs = [
      pkgs.yarn
      node-modules
    ];
    buildPhase = ''
      ln -s ${node-modules}/libexec/node_modules node_modules
      yarn build
    '';
    installPhase = ''
      mkdir $out
      mv dist/* $out
    '';
  };

in

docusaurus-site
