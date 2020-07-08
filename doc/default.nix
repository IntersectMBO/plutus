{ stdenv, lib, pythonPackages, sphinxcontrib-domaintools, sphinxcontrib-haddock, combined-haddock, ... }:
stdenv.mkDerivation {
  name = "plutus-docs";
  src = lib.sourceFilesBySuffices ./. [ ".py" ".rst" ".hs" ];
  buildInputs = [ pythonPackages.sphinx pythonPackages.sphinx_rtd_theme sphinxcontrib-domaintools sphinxcontrib-haddock ];
  buildPhase = ''
    cp -aR ${combined-haddock}/share/doc haddock
    # -n gives warnings on missing link targets, -W makes warnings into errors
    SPHINX_HADDOCK_DIR=haddock sphinx-build -j $NIX_BUILD_CORES -n -W . $out
    cp -aR haddock $out
  '';
  dontInstall = true;
}
