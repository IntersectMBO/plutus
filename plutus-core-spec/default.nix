{ stdenv, lib, texlive }:

let
  tex = texlive.combine {
    inherit (texlive)
    scheme-small
    collection-latexextra
    collection-latexrecommended
    collection-mathscience
    latexmk;
  };
in
stdenv.mkDerivation {
  name = "plutus-core-spec";
  buildInputs = [ tex ];
  src = ./.;
  buildPhase = "latexmk -view=pdf plutus-core-specification.tex";
  installPhase = ''
    install -D plutus-core-specification.pdf $out/plutus-core-specification.pdf
    mkdir -p $out/nix-support
    echo "doc-pdf spec $out/plutus-core-specification.pdf" >> $out/nix-support/hydra-build-products
  '';

  meta = with lib; {
    description = "Plutus Core specification";
    license = licenses.bsd3;
    platforms = platforms.linux;
  };
}
