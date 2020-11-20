{ stdenv
, lib
, nodejs
, easyPS
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
  cleanSrcs = lib.cleanSourceWith {
    filter = lib.cleanSourceFilter;
    src = lib.cleanSourceWith {
      filter = (path: type: !(lib.elem (baseNameOf path)
        [ ".spago" ".spago2nix" "generated" "generated-docs" "output" "dist" "node_modules" ".psci_modules" ".vscode" ]));
      inherit src;
    };
  };

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
