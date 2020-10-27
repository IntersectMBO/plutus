{ pkgs, haskell, easyPS }:
pkgs.recurseIntoAttrs (rec {
  # Packages which are useful during development, but we don't depend upon directly to build our stuff
  packages = pkgs.recurseIntoAttrs {
    # See comment on the definition about it not working
    cabal-install = haskell.extraPackages.cabal-install.components.exes.cabal;
    stylish-haskell = haskell.extraPackages.stylish-haskell.components.exes.stylish-haskell;
    hlint = haskell.extraPackages.hlint.components.exes.hlint;
    haskell-language-server = haskell.extraPackages.haskell-language-server.components.exes.haskell-language-server;
    haskell-language-server-wrapper = haskell.extraPackages.haskell-language-server.components.exes.haskell-language-server-wrapper;
    hie-bios = haskell.extraPackages.hie-bios.components.exes.hie-bios;
    ghcide = haskell.extraPackages.ghcide.components.exes.ghcide;
    purty = haskell.extraPackages.purty.components.exes.purty;
    purs = easyPS.purs;
    spago = easyPS.spago;
  };

  scripts = pkgs.recurseIntoAttrs {
    updateMaterialized = haskell.project.stack-nix.passthru.updateMaterialized;

    fixStylishHaskell = pkgs.writeScriptBin "fix-stylish-haskell" ''
      #!${pkgs.runtimeShell}
      set -eou pipefail

      ${pkgs.git}/bin/git diff > pre-stylish.diff
      ${pkgs.fd}/bin/fd \
        --extension hs \
        --exclude '*/dist/*' \
        --exclude '*/docs/*' \
        --exec ${packages.stylish-haskell}/bin/stylish-haskell -i {}
      ${pkgs.git}/bin/git diff > post-stylish.diff
      if (diff pre-stylish.diff post-stylish.diff > /dev/null)
      then
        echo "Changes by stylish have been made. Please commit them."
      else
        echo "No stylish changes were made."
      fi
      rm pre-stylish.diff post-stylish.diff
      exit
    '';

    fixPurty = pkgs.writeScriptBin "fix-purty" ''
      #!${pkgs.runtimeShell}
      set -eou pipefail

      ${pkgs.git}/bin/git diff > pre-purty.diff
      ${pkgs.fd}/bin/fd \
        --extension purs \
        --exclude '*/.psc-package/*' \
        --exclude '*/.spago/*' \
        --exclude '*/node_modules/*' \
        --exclude '*/generated/*' \
        --exec ${packages.purty}/bin/purty --write {}
      ${pkgs.git}/bin/git diff > post-purty.diff
      if (diff pre-purty.diff post-purty.diff > /dev/null)
      then
        echo "Changes by purty have been made. Please commit them."
      else
        echo "No purty changes were made."
      fi
      rm pre-purty.diff post-purty.diff
      exit
    '';

    # See note on 'easyPS' in 'default.nix'
    updateClientDeps = pkgs.lib.meta.addMetaAttrs { platforms = pkgs.lib.platforms.linux; } (pkgs.writeScriptBin "update-client-deps" ''
      #!${pkgs.runtimeShell}
      set -eou pipefail

      export PATH=${pkgs.gccStdenv.lib.makeBinPath [
        pkgs.coreutils
        pkgs.git
        pkgs.python
        pkgs.gnumake
        pkgs.gnused
        pkgs.nodejs-10_x
        pkgs.nodePackages_10_x.node-gyp
        pkgs.yarn
        # yarn2nix won't seem to build on hydra, see
        # https://github.com/moretea/yarn2nix/pull/103
        # I can't figure out how to fix this...
        pkgs.yarn2nix-moretea.yarn2nix
        easyPS.purs
        easyPS.psc-package
        easyPS.spago
        easyPS.spago2nix
      ]}

      if [ ! -f package.json ]
      then
          echo "package.json not found. Please run this script from the client directory." >&2
          exit 1
      fi

      echo Installing JavaScript Dependencies
      yarn

      echo Generating nix configs.
      yarn2nix > yarn.nix
      spago2nix generate

      echo Done
    '');

    updateMetadataSamples = pkgs.writeScriptBin "update-metadata-samples" ''
      #!${pkgs.runtimeShell}
      set -eou pipefail

      SERVER=https://api.cardano.org/staging
      SUBJECT=7f71940915ea5fe85e840f843c929eba467e6f050475bad1f10b9c274d1888c0
      DATA_DIR=plutus-scb/test/Cardano/Metadata

      ${pkgs.curl}/bin/curl -o $DATA_DIR/subject_response1.json $SERVER/metadata/$SUBJECT

      for PROPERTY in name owner preImage description
      do
        ${pkgs.curl}/bin/curl -o $DATA_DIR/property_$PROPERTY.json $SERVER/metadata/$SUBJECT/properties/$PROPERTY
      done
    '';
  };
})
