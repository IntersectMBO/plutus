#!/usr/bin/env bash

# Build Haddock documentation for all packages in Plutus, includes internal 
# libraries.
#
# Usage: ./build-combined-haddocks.sh DIR [COMPS ...]
#
#   DIR 
#     Where to put the generated pages, the default is 'haddocks'.
#   COMPS 
#     The components to re-build haddocks for, or 'all' to rebuild everything
#     The default is "", which does not rebuild anything (useful for debugging
#     this script).

# set -euo pipefail

OUTPUT_DIR=${1:-haddocks}
REGENERATE=("${@:2}")

BUILD_DIR=dist-newstyle

CABAL_OPTS=(
  --builddir "${BUILD_DIR}"
  --enable-documentation
  --enable-tests
)

# Haddock webpages have a header with the following items: 
#   Quick Jump - Instances - Sources - Contents - Index
# Contents and Index are usually package/component-wide, but this can be overritten.
# In this case we make them point to the top-level, project-wide Contents and Index.
#
# TODO: to also include haddocks for tests, benchmarks and executables, add 
# `--haddock-all` below and fix the odd cabal build failures.
HADDOCK_OPTS=(
  --haddock-internal
  --haddock-html
  --haddock-hyperlink-source
  --haddock-option "--show-all"
  --haddock-option "--pretty-html"
  --haddock-option "--use-unicode"
  --haddock-option="--base-url=.."
  --haddock-option="--use-index=../index.html"
  --haddock-option="--use-contents=../doc-index.html"
  --haddock-quickjump
)

if (( "${#REGENERATE[@]}" > 0 )); then
  cabal build   "${CABAL_OPTS[@]}" "${REGENERATE[@]}"
  cabal haddock "${CABAL_OPTS[@]}" "${REGENERATE[@]}" "${HADDOCK_OPTS[@]}"
fi

mkdir -p "${OUTPUT_DIR}"
chmod -R u+w "${OUTPUT_DIR}"

GHC_VERSION=$(ghc --numeric-version)

OS_ARCH=$(jq -r '"\(.arch)-\(.os)"' "$BUILD_DIR/cache/plan.json")

BUILD_CONTENTS="${BUILD_DIR}/build/${OS_ARCH}/ghc-${GHC_VERSION}"

PLUTUS_VERSION=$(find $BUILD_CONTENTS/plutus-core-* -printf '%f\n' -quit | sed "s/plutus-core-//g")

BASE_VERSION=$(ghc-pkg field base version | cut -c10-)

GIT_REV=$(git rev-parse HEAD)

echo "Copy all relevant content from $BUILD_CONTENTS to $OUTPUT_DIR"
for package_dir in "${BUILD_CONTENTS}"/*; do
  package=$(basename "${package_dir}" | sed 's/-[0-9]\+\(\.[0-9]\+\)*//')
  if [ -d "${package_dir}/doc/html/${package}" ]; then
    cp -rn "${package_dir}/doc/html/${package}" "${OUTPUT_DIR}"
  else 
    # $OUTPUT_DIR/plutus-benchmark isn't created for some reason...
    mkdir -p "${OUTPUT_DIR}/${package}/src"
  fi 

  # Here we merge each package's internal libraries into a single folder, for example:
  # Merge:
  #   plutus-core-1.29.0.0/l/index-envs/*
  #   plutus-core-1.29.0.0/l/plutus-core-execlib/*
  #   plutus-core-1.29.0.0/l/plutus-core-testlib/*
  #   plutus-core-1.29.0.0/l/plutus-ir/*
  #   plutus-core-1.29.0.0/l/plutus-ir-cert/*
  #   plutus-core-1.29.0.0/l/satint/*
  # Into: 
  #   plutus-core/*
  # 
  # The same merging logic applies to source files:
  # Merge: 
  #   plutus-core-1.29.0.0/l/*/src/*
  # Into: 
  #   plutus-core/src/*
  # 
  # Because all modules have unique names, this is safe to do.
  # We don't care that we override the doc-index-*.html files, since we always
  # use the top-level ones.
  if [ -d "${package_dir}/l" ]; then
    for lib_package_dir in "${package_dir}/l"/*; do
      lib_package=$(basename "${lib_package_dir}")
      if [ -d "${lib_package_dir}/doc/html/${package}" ]; then
        mkdir -p "${OUTPUT_DIR}/${package}/${lib_package}"
        cp -n "${lib_package_dir}/doc/html/${package}"/*.html             "${OUTPUT_DIR}/${package}"
        cp -n "${lib_package_dir}/doc/html/${package}/src"/*.html         "${OUTPUT_DIR}/${package}/src"
        cp -f "${lib_package_dir}/doc/html/${package}/src"/{*.js,*.css}   "${OUTPUT_DIR}/${package}/src"
        cp -n "${lib_package_dir}/doc/html/${package}/${package}.haddock" "${OUTPUT_DIR}/${package}/${lib_package}/${package}.haddock"
        cp -n "${lib_package_dir}/doc/html/${package}/doc-index.json"     "${OUTPUT_DIR}/${package}/${lib_package}.doc-index.json"
      fi
    done
  fi

  # # The same for test libs
  # if [ -d "${package_dir}/t" ]; then
  #   for lib_package_dir in "${package_dir}/t"/*; do
  #     lib_package=$(basename "${lib_package_dir}")
  #     if [ -d "${lib_package_dir}/doc/html/${package}" ]; then
  #       mkdir -p "${OUTPUT_DIR}/${package}/${lib_package}"
  #       cp -n "${lib_package_dir}/doc/html/${package}"/*.html             "${OUTPUT_DIR}/${package}"
  #       cp -n "${lib_package_dir}/doc/html/${package}/src"/*.html         "${OUTPUT_DIR}/${package}/src"
  #       cp -f "${lib_package_dir}/doc/html/${package}/src"/{*.js,*.css}   "${OUTPUT_DIR}/${package}/src"
  #       cp -n "${lib_package_dir}/doc/html/${package}/${package}.haddock" "${OUTPUT_DIR}/${package}/${lib_package}/${package}.haddock"
  #       cp -n "${lib_package_dir}/doc/html/${package}/doc-index.json"     "${OUTPUT_DIR}/${package}/${lib_package}.doc-index.json"
  #     fi
  #   done
  # fi
done


echo "Collecting --read-interface options for Haddock"
INTERFACE_OPTIONS=()
for haddock_file in $(find ${OUTPUT_DIR} -name "*.haddock"); do
  package=$(basename -s .haddock "${haddock_file}")
  INTERFACE_OPTIONS+=("--read-interface=${package},${haddock_file}")
done


echo "Writing the Haddock prologue"
cat << EOF > "${BUILD_CONTENTS}/haddock.prologue"
== Handy module entrypoints

  * "PlutusTx": Compiling Haskell to PLC (Plutus Core; on-chain code).
  * "PlutusTx.Prelude": Haskell prelude replacement compatible with PLC.
  * "PlutusCore": Programming language in which scripts on the Cardano blockchain are written.
  * "UntypedPlutusCore": On-chain Plutus code.
EOF


echo "Generating top-level index and contents"
haddock \
  -o "${OUTPUT_DIR}" \
  --title "Combined Plutus ${PLUTUS_VERSION} Documentation" \
  --gen-index \
  --gen-contents \
  --quickjump \
  --prolog "${BUILD_CONTENTS}/haddock.prologue" \
  "${INTERFACE_OPTIONS[@]}"


echo "Assembling top-level doc-index.json"
for file in $(find "${OUTPUT_DIR}" -name "*.doc-index.json"); do
  project=$(basename "$(dirname "$file")");
  jq ".[] | .link = \"${project}/\(.link)\"" "${file}"
done | 
  jq -s . >"${OUTPUT_DIR}/doc-index.json"


echo "Replacing all hrefs to /dist-newstyle" 
for file in $(find $OUTPUT_DIR -type f); do 
  # Unclear why haddock would not resolve these...
  sed -i -E "s|file:///.*dist-newstyle/.*/doc/html/(.*)|../../\1|g" $file
done


echo "Ensuring that all hrefs to /dist-newstyle were replaced"
if grep -qr "dist-newstyle" $OUTPUT_DIR; then 
  echo "internal error: not all href to dist-newstyle were replaced"
  exit 1
fi


echo "Replacing all hrefs to ../base"
for file in $(find $OUTPUT_DIR -type f); do 
  src="../base/(.*)"
  dst="https://hackage.haskell.org/package/base-${BASE_VERSION}/docs/\1"
  sed -i -E "s|$src|$dst|g" $file
done


echo "Checking that all hrefs to ../base were replaced"
if grep -qr "../base" $OUTPUT_DIR; then
  echo "internal error: not all ../base hrefs were replaced"
  exit 1
fi


echo "Replacing all hrefs to /nix/store"
for file in $(find $OUTPUT_DIR -type f); do 
  # From: file:///nix/store/XXXX-ghc-9.6.5-doc/share/doc/ghc-9.6.5/html/libraries/base-4.18.2.1/src/GHC.Base.html
  #   To: https://hackage.haskell.org/base-4.18.2.1/docs/src/GHC.Base.html"
  src="file:///nix/store/.*-ghc-.*-doc/.*/libraries/([^/]*)/(.*)"
  dst="https://hackage.haskell.org/package/\1/docs/\2"
  sed -i -E "s|$src|$dst|g" $file
done


echo "Checking that all hrefs to /nix/store were replaced"
if grep -qr "/nix/store" $OUTPUT_DIR; then
  echo "internal error: not all /nix/store hrefs were replaced"
  exit 1
fi


# echo "Checking for broken links"
# blc $OUTPUT_DIR/index.html -ro