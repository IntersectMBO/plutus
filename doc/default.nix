{ stdenv
, lib
, pythonPackages
, sphinxcontrib-domaintools
, sphinxcontrib-haddock
, sphinx-markdown-tables
, sphinxemoji
, combined-haddock
, ...
}:
stdenv.mkDerivation {
  name = "plutus-docs";
  src = lib.sourceFilesBySuffices ./. [ ".py" ".rst" ".hs" ".png" ".svg" ".bib" ".csv" ".css" ];
  buildInputs = with pythonPackages; [
    sphinx
    sphinx_rtd_theme
    sphinxcontrib-domaintools
    sphinxcontrib-haddock
    sphinx-markdown-tables
    sphinxcontrib_plantuml
    sphinxcontrib-bibtex
    sphinxemoji
    recommonmark
  ];
  buildPhase = ''
    # FIXME
    # https://input-output.atlassian.net/browse/PLT-789
    # https://hydra.iohk.io/build/18701775/nixlog/1
    echo TODO > $out
    exit 0

    cp -aR ${combined-haddock}/share/doc haddock
    # -n gives warnings on missing link targets, -W makes warnings into errors
    SPHINX_HADDOCK_DIR=haddock sphinx-build -n -W . $out
    cp -aR haddock $out
  '';
  dontInstall = true;
}
