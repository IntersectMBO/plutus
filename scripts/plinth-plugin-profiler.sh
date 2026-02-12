# CURRENT STATE
# To profile the plugin, we need a GHC that has itself been compiled with profiling enabled.
# That we get from the ghc96-plugin shell
# Invoking ghc with +RTS -pj -RTS works, it traces custom SCC added to PlutusTx/Plugin.hs and the .prof
# file can be loaded into speedscope.app 
# The ghc command can be found by inspecting the output of `cabal build -v`.
# However invoking ghc explicitely is brittle, we'd like to be able to rely on cabal.
# However cabal build --ghc-options="+RTS .. -RTS" does not work, as it does not pass those options to GHC itself,
# but to the exec/teststuite/benchmark being built, instead.
# This script is a draft attempt to work around all this.
# Must be noted also that some modules inside plutus-tx-plugin-test break with "GHC.Core to PLC errors".

set -euo pipefail


if ghc --info | grep -q ',("GHC Profiled","YES")'; then
    echo "Profiled GHC detected"
else
    echo "You are not in the right nix shell. Run: nix develop #ghc96-plugin"
fi

ROOT="$(git rev-parse --show-toplevel)"
CABAL_BUILDDIR="$ROOT/dist-newstyle/build/ghc96-profiled"
mkdir -p "$CABAL_BUILDDIR"

GHC_WRAPPER="$CABAL_BUILDDIR/ghc"

echo "#!$(which bash)"                                                       > $GHC_WRAPPER
echo 'PROF_FILE_OUTPUT="ghc-$(date +"%Y.%m.%d-%H:%M:%S")"'                  >> $GHC_WRAPPER
echo 'exec ghc "$@" -with-rtsopts "+RTS -pj -po$PROF_FILE_OUTPUT -I1 -RTS"' >> $GHC_WRAPPER

chmod +x "$GHC_WRAPPER"

cabal --builddir="$CABAL_BUILDDIR" build plutus-tx-plugin-tests --with-ghc="$GHC_WRAPPER"