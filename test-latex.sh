TARGETS=(
    "cost-model-notes cost-model-notes.pdf doc/notes/cost-model-notes"
    "eutxo-paper eutxo.pdf doc/papers/eutxo"
    "eutxoma-paper eutxoma.pdf doc/papers/eutxoma"
    "extended-utxo-spec extended-utxo-specification.pdf doc/extended-utxo-spec"
    "lazy-machine-notes lazy-plutus-core.pdf doc/notes/fomega/lazy-machine"
    "multi-currency-notes multi-currency.pdf doc/notes/multi-currency"
    "plutus-core-spec-old plutus-core-specification.pdf doc/plutus-core-spec-old"
    "plutus-core-spec plutus-core-specification.pdf doc/plutus-core-spec"
    "plutus-report plutus.pdf doc/plutus-report"
    "utxoma-paper utxoma.pdf doc/papers/utxoma"
    "system-f-in-agda-paper system-f-in-agda.pdf doc/papers/system-f-in-agda"
    "unraveling-recursion-paper unraveling-recursion.pdf doc/papers/unraveling-recursion"
)

OUTDIR=$(realpath test-latex)
mkdir $OUTDIR
rm $OUTDIR/*.pdf

for TARGET in "${TARGETS[@]}"; do
    IFS=' ' read -r NIX_NAME PDF_NAME FOLDER <<< "$TARGET"
    pushd $FOLDER 
    make clean 
    make  
    cp $PDF_NAME "$OUTDIR/$NIX_NAME-shell.pdf"
    nix build .#$NIX_NAME 
    cp result/$PDF_NAME.pdf $OUTDIR/$NIX_NAME-nix.pdf
    popd
done