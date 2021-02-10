{ stdenv, lib, texlive }: {
  # Build a latex derivation using latexmk.
  buildLatex =
    { texFiles ? [ ]
    , # The specific tex files to build, will try and build all of them if absent
      texInputs ? { inherit (texlive) scheme-small; }
    , # Tex dependencies as an attrset
      buildInputs ? [ ]
    , # Additional build inputs
      ...
    }@attrs:
    let
      tex = texlive.combine (texInputs // { inherit (texlive) latexmk; });
      # mkDerivation doesn't like having this as an attr, and we don't need to pass it through
      filteredAttrs = builtins.removeAttrs attrs [ "texInputs" ];
      buildDir = ".nix-build";
    in
    stdenv.mkDerivation (filteredAttrs // {
      buildInputs = [ tex ] ++ buildInputs;
      buildPhase = ''
        runHook preBuild
        mkdir -p ${buildDir}
        # The bibtex_fudge setting is because our version of latexmk has an issue with bibtex
        # and explicit output directories, which should be fixed in v4.70b: 
        # https://tex.stackexchange.com/questions/564626/latexmk-4-70a-doesnt-compile-document-with-bibtex-citation
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
    });
  # A typical good filter for latex sources. This also includes files for cases where agda sources are being compiled
  filterLatex = src: lib.sourceFilesBySuffices src [ ".tex" ".bib" ".cls" ".bst" ".pdf" ".png" ".agda" ".agda-lib" ".lagda" ];
}
