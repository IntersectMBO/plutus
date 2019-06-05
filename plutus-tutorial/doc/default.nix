{ stdenv, lib, asciidoctor, python2, playgroundUrl ? null, haddockUrl ? null }:

let
  extraArgs = (lib.optionals (playgroundUrl != null) [ "-a" "playground=${playgroundUrl}" ]) ++ (lib.optionals (haddockUrl != null) [ "-a" "haddock=${haddockUrl}" ]);
in stdenv.mkDerivation {
  name = "plutus-tutorial";
  src = lib.sourceFilesBySuffices ./. [ ".adoc" ".png" ".PNG" ".gif" ".ico" ".css" ];
  buildInputs = [ asciidoctor python2 ];
  buildPhase = "asciidoctor ${toString extraArgs} index.adoc";
  installPhase = ''
    mkdir -p $out
    install -t $out *.html 
    cp -aR images $out
    cp -aR css $out
  '';
}
