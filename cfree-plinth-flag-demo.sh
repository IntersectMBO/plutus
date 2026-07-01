#!/usr/bin/env bash
#
# cfree-plinth-flag-demo.sh
#
# Demonstrate that a Plinth script (IntersectMBO/plinth-template) can be WRITTEN
# and COMPILED with NO system cryptography C libraries (libsodium / libblst /
# libsecp256k1), in a self-contained non-nix sandbox, using ONLY the new
# `with-crypto` Cabal flag on plutus-core.
#
# Unlike the sub-library carve, the consumer makes NO source or .cabal changes:
# plinth-template depends on the ordinary plutus-core / plutus-tx /
# plutus-ledger-api / plutus-tx-plugin and merely sets
#
#     package plutus-core
#       flags: -with-crypto
#
# in its cabal.project. The flag drops cardano-crypto-class (and therefore the C
# libraries) from plutus-core's dependency closure; the cryptographic builtins
# become compile-only stubs.
#
# It:
#   1. Creates an isolated sandbox (its own ghcup + cabal store).
#   2. Downloads GHC 9.6.7 + cabal from ghcup (the web).
#   3. sdist's the monorepo plutus packages into a local file+noindex repo.
#   4. Clones plinth-template UNMODIFIED and adds only the -with-crypto flag.
#   5. Solves + builds, asserting cardano-crypto-class is never solved or built.
#   6. Runs the compiled validator to emit a CIP-57 blueprint.
#
# Usage:   ./cfree-plinth-flag-demo.sh
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUTUS_REPO="${PLUTUS_REPO:-$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)}"
SANDBOX="${SANDBOX:-/tmp/plinth-flag-sandbox}"

GHC_VERSION="${GHC_VERSION:-9.6.7}"
CABAL_VERSION="${CABAL_VERSION:-3.14.2.0}"
PLINTH_TEMPLATE_URL="https://github.com/IntersectMBO/plinth-template.git"

# index-states matching the monorepo's cabal.project.
HACKAGE_INDEX="2026-06-22T23:30:49Z"
CHAP_INDEX="2026-06-18T17:45:00Z"

# The monorepo packages plinth-template depends on (transitively). Only
# plutus-core carries the with-crypto flag; the rest inherit C-free-ness.
PLUTUS_PKGS=(plutus-core plutus-tx plutus-tx-plugin plutus-ledger-api)

say() { printf '\n\033[1;36m== %s ==\033[0m\n' "$*"; }
die() { printf '\n\033[1;31mFAIL: %s\033[0m\n' "$*" >&2; exit 1; }

# ---------------------------------------------------------------------------
# 1. Isolated sandbox
# ---------------------------------------------------------------------------
say "1. Creating isolated sandbox at $SANDBOX"
mkdir -p "$SANDBOX"
export GHCUP_INSTALL_BASE_PREFIX="$SANDBOX"
export CABAL_DIR="$SANDBOX/.cabal"
export BOOTSTRAP_HASKELL_NONINTERACTIVE=1
export BOOTSTRAP_HASKELL_NO_UPGRADE=1
export BOOTSTRAP_HASKELL_ADJUST_BASHRC=0
export BOOTSTRAP_HASKELL_INSTALL_NO_STACK=1
export BOOTSTRAP_HASKELL_GHC_VERSION="$GHC_VERSION"
export BOOTSTRAP_HASKELL_CABAL_VERSION="$CABAL_VERSION"
GHCUP_BIN="$SANDBOX/.ghcup/bin"
[ -d "$PLUTUS_REPO/plutus-core" ] || die "PLUTUS_REPO ($PLUTUS_REPO) is not the plutus monorepo"

# ---------------------------------------------------------------------------
# 2. ghcup + GHC + cabal from the web
# ---------------------------------------------------------------------------
say "2. Installing ghcup + GHC $GHC_VERSION + cabal $CABAL_VERSION"
if [ ! -x "$GHCUP_BIN/ghcup" ]; then
  curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
fi
export PATH="$GHCUP_BIN:$PATH"
ghcup install ghc   "$GHC_VERSION"   --set || true
ghcup install cabal "$CABAL_VERSION" --set || true
hash -r 2>/dev/null || true
ghc   --version >/dev/null 2>&1 || ghcup install ghc   "$GHC_VERSION"   --force --set
cabal --version >/dev/null 2>&1 || ghcup install cabal "$CABAL_VERSION" --force --set
hash -r 2>/dev/null || true
say "Toolchain:"; ghc --version; cabal --version
cabal update

# ---------------------------------------------------------------------------
# 3. Show the host has NO crypto C libraries
# ---------------------------------------------------------------------------
say "3. System cryptography C libraries on this host"
for lib in libblst libsodium libsecp256k1; do
  if command -v pkg-config >/dev/null 2>&1 && pkg-config --exists "$lib" 2>/dev/null; then
    printf '   %-14s PRESENT\n' "$lib"
  else
    printf '   %-14s absent\n' "$lib"
  fi
done
echo "   (the C-free build below must not need any of them; we assert"
echo "    cardano-crypto-class is never solved or built.)"

# ---------------------------------------------------------------------------
# 4. sdist the monorepo plutus packages into a local repo
# ---------------------------------------------------------------------------
say "4. Building source tarballs of the monorepo plutus packages -> file+noindex repo"
REPO="$SANDBOX/local-plutus-repo"
rm -rf "$REPO"; mkdir -p "$REPO"
SDIST_PROJECT="$SANDBOX/cabal.project.sdist"
{ echo "packages:"; for p in "${PLUTUS_PKGS[@]}"; do echo "  $PLUTUS_REPO/$p"; done; } > "$SDIST_PROJECT"
cabal sdist --project-file="$SDIST_PROJECT" "${PLUTUS_PKGS[@]}" --output-dir "$REPO"
ls -1 "$REPO"/*.tar.gz

# ---------------------------------------------------------------------------
# 5. Clone plinth-template UNMODIFIED; add only the -with-crypto flag
# ---------------------------------------------------------------------------
say "5. Cloning plinth-template (no source/.cabal changes) and setting -with-crypto"
cd "$SANDBOX"
rm -rf plinth-template
git clone --depth 1 "$PLINTH_TEMPLATE_URL" plinth-template
cd plinth-template

cat > cabal.project <<EOF
repository cardano-haskell-packages
  url: https://chap.intersectmbo.org/
  secure: True
  root-keys:
    3e0cce471cf09815f930210f7827266fd09045445d65923e6d0238a6cd15126f
    443abb7fb497a134c343faf52f0b659bd7999bc06b7f63fa76dc99d631f9bea1
    a86a1f6ce86c449c46666bda44268677abf29b5b2d2eb5ec7af903ec2f117a82
    bcec67e8e99cabfa7764d75ad9b158d72bfacf70ca1d0ec8bc6b4406d1bf8413
    c00aae8461a256275598500ea0e187588c35a5d5d7454fb57eac18d9edb86a56
    d4a35cd3121aa00d18544bb0ac01c3e1691d618f462c46129271bccf39f7e8ee

repository local-plutus
  url: file+noindex://$REPO

index-state:
  , hackage.haskell.org $HACKAGE_INDEX
  , cardano-haskell-packages $CHAP_INDEX

active-repositories:
  , hackage.haskell.org
  , cardano-haskell-packages
  , local-plutus:override

packages: ./.

-- The ONLY change a C-free script author makes: drop the system cryptography
-- backend from plutus-core. Scripts still compile; crypto builtins can't be
-- evaluated off-chain in this build.
package plutus-core
  flags: -with-crypto

constraints: setup.optparse-applicative >=0.19.0.0

-- Mirror the monorepo cabal.project's allow-newer (needed at this index-state,
-- e.g. deriving-aeson hasn't bumped its aeson upper bound).
allow-newer:
  , deriving-aeson:aeson
  , microstache:aeson
  , turtle:containers
  , turtle:optparse-applicative
EOF

# ---------------------------------------------------------------------------
# 6. Solve (must be crypto-free)
# ---------------------------------------------------------------------------
say "6. Checking the build plan is crypto-free"
cabal update
PLAN="$(cabal build all --dry-run 2>&1)"
echo "$PLAN" | grep -E "plutus-(core|tx|ledger-api)" || true
if echo "$PLAN" | grep -qi "cardano-crypto-class"; then
  echo "$PLAN" | grep -i "cardano-crypto-class"
  die "build plan pulls cardano-crypto-class -> NOT C-free"
fi
echo "   -> build plan contains NO cardano-crypto-class. C-free solve confirmed."

# ---------------------------------------------------------------------------
# 7. Build and assert cardano-crypto-class is never built
# ---------------------------------------------------------------------------
say "7. Building plinth-template (no crypto C libraries)"
BUILD_LOG="$SANDBOX/build.log"
cabal build all 2>&1 | tee "$BUILD_LOG"
grep -qiE "cardano-crypto-class.* \((lib|exe)" "$BUILD_LOG" \
  && die "cardano-crypto-class was built -> NOT C-free" || true
grep -qE "Compiling AuctionValidator" "$BUILD_LOG" \
  || die "the Plinth validator was not compiled by the plugin"
echo "   -> plugin compiled the Plinth scripts; cardano-crypto-class was never built."

# ---------------------------------------------------------------------------
# 8. Run the C-free-compiled validator: emit a CIP-57 blueprint
# ---------------------------------------------------------------------------
say "8. Running the C-free-compiled validator to emit a blueprint"
OUT="$SANDBOX/auction-blueprint.json"
cabal run -v0 gen-auction-validator-blueprint -- "$OUT"
[ -s "$OUT" ] || die "no blueprint produced"
echo "   -> wrote $(wc -c < "$OUT") bytes to $OUT"
head -c 300 "$OUT"; echo

say "SUCCESS"
cat <<EOF

A Plinth script (plinth-template's auction validator) was written, compiled to
UPLC by the plugin, and emitted as a CIP-57 blueprint -- using GHC $GHC_VERSION and
cabal from ghcup, in an isolated sandbox, with NO system cryptography C
libraries solved or built. The ONLY consumer change was

  package plutus-core
    flags: -with-crypto

  sandbox:    $SANDBOX
  blueprint:  $OUT
EOF
