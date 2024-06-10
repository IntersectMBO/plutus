# This script generates a local, self-contained, deployable Haddock for the
# Plutus project. It uses the experimental 'haddock-project' Cabal command,
# which currently has some issues that need fixing. 

# Setup source directory 
SRC=combined_haddock_src
rm -rf $SRC
mkdir -p $SRC

# Write haddock prologue 
cat << EOF > $SRC/haddock.prologue
= Combined Plutus Documentation
    
* "PlutusTx": Compiling Haskell to PLC (Plutus Core; on-chain code).
* "PlutusTx.Prelude": Haskell prelude replacement compatible with PLC.
* "PlutusCore": Programming language in which scripts on the Cardano blockchain are written.
* "UntypedPlutusCore": On-chain Plutus code.
EOF

# Clean project and build haddock
cabal clean 
cabal update
cabal build all
cabal haddock-project \
  --quickjump \
  --gen-contents \
  --hyperlinked-source \
  --gen-index \
  --internal \
  --output=$SRC \
  --prologue=$SRC/haddock.prologue

# Setup destination directory 
DST=combined_haddock_dst
rm -rf $DST
mkdir -p $DST

# List of target haskell packages 
PACKAGE_DIRS=$(find $SRC -maxdepth 1 -mindepth 1 -type d -exec basename {} \; | sed -E 's/-[0-9].*$//' | sort -u)

# Merge each package's sublibraries into a single folder, for example:
# Merge:
#   plutus-core-1.28.0.0-inplace/*
#   plutus-core-1.28.0.0-inplace-index-envs/*
#   plutus-core-1.28.0.0-inplace-plutus-core-execlib/*
#   ...
# Into: 
#   plutus-core/* 
for NAME in $PACKAGE_NAMES; do 
  mkdir -p $DST/$NAME/src
  SUBLIBS=$(find $SRC -type d -name "$NAME*" -print)
  for SUBLIB in $SUBLIBS; do 
    cp -R $SUBLIB/* $DST/$NAME
  done 
done 

# Copy the top-level static files 
cp -R $SRC/{*.html,*.js,*.css,*.png} $DST

# Replace all /nix/store hrefs for ghc documentation in the destination folder.
for NAME in "${PACKAGE_NAMES[@]}"; do 
  find "$DST/$NAME" -type f -name "*.html" | while read -r FILE; do
    sed -i -E "s|file:///nix/store/.*-ghc-.*-doc/.*/libraries/([^0-9]*)-[0-9][^/]*/(.*)|../../\1/\2|g" $FILE
  done
done 

# Ensure that all /nix/store hrefs were replaced
if grep -q -R -E "/nix/store/.*" $DST; then
  echo "internal error: not all /nix/store hrefs were replaced"
  exit 1
fi

# Replace all dist-newstyle hrefs in the destination folder. 
for NAME in "${PACKAGE_NAMES[@]}"; do 
  find "$DST/$NAME" -type f -name "*.html" | while read -r FILE; do
    sed -i -E "s|file:///.*dist-newstyle/.*/doc/html/(.*)|../../\1|g" $FILE
  done
done 

# Ensure that all dist-newstyle hrefs were replaced
if grep -q -R -E "/dist-newstyle/.*" $DST; then
  echo "internal error: not all /dist-newstyle hrefs were replaced"
  exit 1
fi

# Produce the aggregated doc-index.json
shopt -s globstar
echo "[]" > "$DST/doc-index.json"
for file in $(ls $DST/**/doc-index.json); do
  PROJECT=$(dirname $file);
  EXPR=".[0] + [.[1][] | (. + {link: (\"$project/\" + .link)}) ]"
  jq -s "$EXPR" "$DST/doc-index.json" "$file" > $DST/doc-index.tmp.json
  mv $DST/doc-index.tmp.json "$DST/doc-index.json"
done