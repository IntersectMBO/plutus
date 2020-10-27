{ stdenv, lib, asciidoctor, python2, plutusPlaygroundUrl ? null, marlowePlaygroundUrl ? null, ... }:

let
  extraArgs = (lib.optionals (plutusPlaygroundUrl != null) [ "-a" "plutusplayground=${plutusPlaygroundUrl}" ]) ++ (lib.optionals (marlowePlaygroundUrl != null) [ "-a" "marloweplayground=${marlowePlaygroundUrl}" ]);
in
stdenv.mkDerivation {
  name = "marlowe-tutorial";
  src = lib.sourceFilesBySuffices ./. [ ".adoc" ".svg" ".png" ".PNG" ".gif" ".ico" ".css" ];
  buildInputs = [ asciidoctor python2 ];
  buildPhase = "asciidoctor --failure-level ERROR ${toString extraArgs} index.adoc";
  installPhase = ''
    mkdir -p $out
    install -t $out *.html 
    cp -aR images $out
    cp -aR css $out
  '';
}
