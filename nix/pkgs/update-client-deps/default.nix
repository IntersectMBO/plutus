{ lib
, writeScriptBin
, runtimeShell
, git
, fd
, purty
, coreutils
, python
, gnumake
, gnused
, nodejs-10_x
, node-gyp
, yarn
, yarn2nix
, purs
, psc-package
, spago
, spago2nix
, isDarwin
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
    nodejs-10_x
    node-gyp
    yarn
    # yarn2nix won't seem to build on hydra, see
    # https://github.com/moretea/yarn2nix/pull/103
    # I can't figure out how to fix this...
    yarn2nix
    purs
    psc-package
    spago
    spago2nix
  ] ++ lib.optionals isDarwin [ clang ])}

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
