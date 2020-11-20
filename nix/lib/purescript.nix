{ stdenv
, lib
, nodejs
, easyPS
, nix-gitignore
, buildNodeModules
}:

{ psSrc
, src
, name
, additionalPurescriptSources ? [ ]
, additionalNpmBuildInputs ? [ ]
, packages
, spagoPackages
, webCommon
, checkPhase ? ""
}:
let
  # Cleans the source based on the patterns in ./.gitignore and
  # the additionalIgnores
  cleanSrcs =
    let
      additionalIgnores = ''
        /*.adoc
        /*.nix
      '';
    in
    nix-gitignore.gitignoreSource additionalIgnores src;

  # All sources to be passed to `purs`
  purescriptSources = [
    "src/**/*.purs"
    "test/**/*.purs"
    "generated/**/*.purs"
    ".spago/*/*/src/**/*.purs"
  ] ++ additionalPurescriptSources;

  nodeModules = buildNodeModules { projectDir = src; buildInputs = additionalNpmBuildInputs; };
in
stdenv.mkDerivation {
  name = "plutus-playground-client";
  src = cleanSrcs;
  buildInputs = [ nodeModules easyPS.purs easyPS.spago easyPS.psc-package ];
  buildPhase = ''
    export HOME=$NIX_BUILD_TOP
    shopt -s globstar
    ln -s ${nodeModules}/node_modules node_modules
    ln -s ${psSrc} generated
    ln -s ${webCommon} ../web-common

    sh ${spagoPackages.installSpagoStyle}
    purs compile ${builtins.concatStringsSep " " purescriptSources}
    npm run webpack
  '';
  installPhase = ''
    mv dist $out
  '';
  doCheck = true;
}
