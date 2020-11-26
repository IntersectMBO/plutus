{ stdenv
, lib
, writeScriptBin
, runtimeShell
, git
, fd
, coreutils
, python
, gnumake
, gnused
, nodejs
, nodePackages
, purs
, psc-package
, spago
, spago2nix
, clang
}:

lib.meta.addMetaAttrs { platforms = lib.platforms.linux; } (writeScriptBin "update-client-deps" ''
  #!${runtimeShell}
  set -eou pipefail

  export PATH=${lib.makeBinPath ([
    coreutils
    git
    python
    gnumake
    gnused
    nodejs
    nodePackages.node-gyp
    purs
    psc-package
    spago
    spago2nix
  ] ++ lib.optionals stdenv.isDarwin [ clang ])}

  if [ ! -f spago.dhall ]
  then
      echo "spago.dhall not found. Please run this script from the client directory." >&2
      exit 1
  fi

  echo Generating nix configs.
  spago2nix generate

  echo Done
'')
