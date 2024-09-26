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
      export HOME=$(pwd)
      ln -s ${node-modules}/libexec/docusaurus/node_modules node_modules
      yarn
      yarn build
    '';
    installPhase = ''
      mkdir $out
      mv dist/* $out
    '';
  };

in

{ inherit node-modules docusaurus-site; }
