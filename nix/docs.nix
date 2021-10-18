{ pkgs, plutus-apps }:
pkgs.recurseIntoAttrs {
  site = pkgs.callPackage ../doc {
    inherit (plutus-apps) sphinx-markdown-tables sphinxemoji;
    inherit (plutus-apps.sphinxcontrib-haddock) sphinxcontrib-haddock sphinxcontrib-domaintools;
    combined-haddock = plutus-apps.plutus-haddock-combined;
    pythonPackages = pkgs.python3Packages;
  };

  build-and-serve-docs = pkgs.writeShellScriptBin "build-and-serve-docs" ''
    cd $(nix-build default.nix -A docs.site) && \
    ${pkgs.python3}/bin/python3 -m http.server 8002
  '';
}
