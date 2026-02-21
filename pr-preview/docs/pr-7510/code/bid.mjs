import cbor from 'cbor'
import {
  BlockfrostProvider,
  MeshWallet,
  Transaction,
  deserializeDatum,
  hexToString,
  serializePlutusScript,
  resolveScriptHash,
  stringToHex
} from '@meshsdk/core'

import fs from 'node:fs'

const blockfrostKey = 'Replace with Blockfrost Project ID'
const blockchainProvider = new BlockfrostProvider(blockfrostKey)

const previousTxHash = process.argv[2]
const bidder = process.argv[3]
const bidAmt = process.argv[4]

const wallet = new MeshWallet({
  networkId: 0,
  fetcher: blockchainProvider,
  submitter: blockchainProvider,
  key: {
    type: 'root',
    bech32: fs.readFileSync(`${bidder}.skey`).toString().trim()
  }
})

const bidderAddr = fs.readFileSync(`${bidder}.addr`).toString()
const bidderPkh = fs.readFileSync(`${bidder}.pkh`).toString()

const auctionValidatorBlueprint = JSON.parse(
  fs.readFileSync('./plutus-auction-validator.json')
)

const auctionValidator = {
  code: cbor
    .encode(
      Buffer.from(auctionValidatorBlueprint.validators[0].compiledCode, 'hex')
    )
    .toString('hex'),
  version: 'V2'
}

const auctionValidatorAddress = serializePlutusScript(auctionValidator).address

const mintingPolicyBlueprint = JSON.parse(
  fs.readFileSync('./plutus-auction-minting-policy.json')
)

const mintingPolicy = {
  code: cbor
    .encode(
      Buffer.from(mintingPolicyBlueprint.validators[0].compiledCode, 'hex')
    )
    .toString('hex'),
  version: 'V2'
}

const mintingPolicyHash = resolveScriptHash(
  mintingPolicy.code,
  mintingPolicy.version
)

const utxos = await blockchainProvider.fetchAddressUTxOs(
  auctionValidatorAddress
)

const utxoIn = utxos.find(utxo => {
  return utxo.input.txHash == previousTxHash
})

if (!utxoIn) throw new Error(`utxo not found for ${previousTxHash}`)

const datumIn = deserializeDatum(utxoIn.output.plutusData)

var highestBidderAddress
var highestBidAmount

if (datumIn.fields.length > 0) {
  highestBidderAddress = hexToString(datumIn.fields[0].fields[0].bytes)
  highestBidAmount = datumIn.fields[0].fields[2].int
}

const bid = {
  alternative: 0,
  fields: [bidderAddr, bidderPkh, parseInt(bidAmt)]
}

const redeemer = {
  data: {
    alternative: 0,
    fields: [bid]
  }
}

const datumOut = {
  alternative: 0,
  fields: [bid]
}

const tx = new Transaction({ initiator: wallet })
  .redeemValue({
    value: utxoIn,
    script: auctionValidator,
    redeemer: redeemer
  })
  .sendAssets(
    {
      address: auctionValidatorAddress,
      datum: { value: datumOut, inline: true }
    },
    [
      {
        unit: 'lovelace',
        quantity: bidAmt
      },
      {
        unit: mintingPolicyHash + stringToHex('TokenToBeAuctioned'),
        quantity: '1'
      }
    ]
  )
  .setTimeToExpire('Replace with transaction expiration time')

if (highestBidderAddress) {
  tx.sendLovelace(highestBidderAddress, highestBidAmount.toString())
}

const unsignedTx = await tx.build()
const signedTx = await wallet.signTx(unsignedTx)
const txHash = await wallet.submitTx(signedTx)

console.log(`Bid successful. Tx hash: ${txHash}`)
