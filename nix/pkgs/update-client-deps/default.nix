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
, yarn
, yarn2nix-moretea
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
    yarn
    yarn2nix-moretea.yarn2nix
    purs
    psc-package
    spago
    spago2nix
  ] ++ lib.optionals stdenv.isDarwin [ clang ])}

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
'')
