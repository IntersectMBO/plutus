{ stdenv, lib, texlive }:
{
  # Build a latex derivation using latexmk.
  buildLatex = { 
    texFiles ? [], # The specific tex files to build, will try and build all of them if absent
    texInputs ? { inherit (texlive) scheme-small; }, # Tex dependencies as an attrset
    buildInputs ? [], # Additional build inputs
    ...}@attrs :

    let 
      tex = texlive.combine (texInputs // { inherit (texlive) latexmk; });
      # mkDerivation doesn't like having this as an attr, and we don't need to pass it through
      filteredAttrs = builtins.removeAttrs attrs ["texInputs" ];
      buildDir = ".nix-build";
    in
    stdenv.mkDerivation (filteredAttrs // {
      buildInputs = [ tex ] ++ buildInputs;
      buildPhase = ''
        runHook preBuild
        mkdir -p ${buildDir}
        latexmk -outdir=${buildDir} -pdf ${toString texFiles}
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
  # A typical good filter for latex sources.
  filterLatex = src: lib.sourceFilesBySuffices src [ ".tex" ".bib" ".cls" ".bst" ".pdf" ".png" ];
}
