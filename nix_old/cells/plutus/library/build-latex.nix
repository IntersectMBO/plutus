{ inputs, cell }:

let
  inherit (cell.library) pkgs;
in

# Build a latex derivation using latexmk.
{ texFiles ? [ ]
, # The specific tex files to build, will try and build all of them if absent
  texInputs ? { inherit (pkgs.texlive) scheme-small; }
, # Tex dependencies as an attrset
  buildInputs ? [ ]
, # Additional build inputs
  ...
}@attrs:
let
  tex = pkgs.texlive.combine (texInputs // { inherit (pkgs.texlive) latexmk; });

  # mkDerivation doesn't like having this as an attr, and we don't need to pass it through
  filteredAttrs = builtins.removeAttrs attrs [ "texInputs" ];

  buildDir = ".nix-build";
in
pkgs.stdenv.mkDerivation (filteredAttrs // {

  buildInputs = [ tex ] ++ buildInputs;

  buildPhase = ''
    runHook preBuild
    mkdir -p ${buildDir}
    # The bibtex_fudge setting is because our version of latexmk has an issue with bibtex
    # and explicit output directories, which should be fixed in v4.70b:
    # https://tex.stackexchange.com/questions/564626/latexmk-4-70a-doesnt-compile-document-with-bibtex-citation # editorconfig-checker-disable-line
    latexmk \
      -e '$bibtex_fudge=1' \
      -outdir=${buildDir} \
      -pdf \
      ${toString texFiles}
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p $out
    install -t $out ${buildDir}/*.pdf

    mkdir -p $out/nix-support
    for pdf in $out/*.pdf; do
      echo "doc-pdf $(basename $pdf .pdf) $pdf" >> $out/nix-support/hydra-build-products
    done
    runHook postInstall
  '';
})
