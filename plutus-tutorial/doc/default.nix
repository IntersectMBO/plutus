{ stdenv, lib, asciidoctor, python2, plutusPlaygroundUrl ? null, haddockUrl ? null, ... }:

let
  extraArgs = (lib.optionals (plutusPlaygroundUrl != null) [ "-a" "playground=${plutusPlaygroundUrl}" ]) ++ (lib.optionals (haddockUrl != null) [ "-a" "haddock=${haddockUrl}" ]);
in stdenv.mkDerivation {
  name = "plutus-tutorial";
  src = lib.sourceFilesBySuffices ./. [ ".adoc" ".png" ".PNG" ".gif" ".ico" ".css" ];
  buildInputs = [ asciidoctor python2 ];
  buildPhase = "asciidoctor --failure-level ERROR ${toString extraArgs} index.adoc";
  installPhase = ''
    mkdir -p $out
    install -t $out *.html 
    cp -aR images $out
    cp -aR css $out
  '';
}
