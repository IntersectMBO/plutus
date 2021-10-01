#!/usr/bin/env bash
set -euo pipefail

export PATH=$(pwd)/cardano-cli/bin:$PATH
magic="--testnet-magic=8"

workdir=$(pwd)/dumpdir
walletdir=$(pwd)

script=$(pwd)/uniswapCurrency.plutus
scriptaddr=$workdir/issue.addr

mintingpolicyjson=$workdir/minting-policy.json
paymentaddr="addr_test1qq0ftd6dpmnwwqfxxa8m4jh0x5wt45h6tt024x8n33hl5lu2t9pjmxa37enmy9wt8pk5h0tje3chs6sr8qljf0sfah3qqhfd5f"
paymentvkey=$walletdir/payment.vkey
paymentskey=$walletdir/payment.skey

# set txhash & txix from utxo available @ $paymentaddr
txhash=9cbf810d18f1737fdb455ced40cf5f2b6c7c350de89d41a43493297900ca4ce5
txix=0
txmint=$workdir/txmint

echo "UTXOs @ $paymentaddr"
cardano-cli query utxo --address $paymentaddr $magic
cardano-cli address build --payment-script-file $script --out-file $scriptaddr $magic

echo "Script addr: $scriptaddr"
echo -e '\n\n'

cat >$mintingpolicyjson <<EOL
{
  "keyHash": "$(cardano-cli address key-hash --payment-verification-key-file $paymentvkey)",
  "type": "sig"
}
EOL

currencysymbol=$(cardano-cli transaction policyid --script-file $mintingpolicyjson)

amount=5000000
tokenList=""
tokens=(Pika Char Bul Colin)
for i in "${!tokens[@]}"; do
  tokenList="${tokenList}"+"${amount} ${currencysymbol}.${tokens[i]}"
done
tokenList="${tokenList#+}"

echo "     Token List: $tokenList"
echo "Currency Symbol: $currencysymbol"
echo " Minting Policy: $(cat $mintingpolicyjson)"


cardano-cli transaction build \
    --alonzo-era \
    --tx-in $txhash#$txix \
    --tx-out $paymentaddr+2000000+"$tokenList" \
    --mint "$tokenList" \
    --mint-script-file $mintingpolicyjson \
    --change-address $paymentaddr \
    $magic \
    --out-file $txmint.raw

cardano-cli transaction sign \
    --tx-body-file $txmint.raw \
    --signing-key-file $paymentskey \
    $magic \
    --out-file $txmint.sign

cat $txmint.raw
cat $txmint.sign
cardano-cli transaction submit $magic --tx-file $txmint.sign
