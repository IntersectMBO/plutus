import cbor from 'cbor'
import {
  BlockfrostProvider,
  MeshWallet,
  Transaction,
  serializePlutusScript,
} from '@meshsdk/core'

import fs from 'node:fs'

const blockfrostKey = 'Replace with Blockfrost Project ID'
const blockchainProvider = new BlockfrostProvider(blockfrostKey)

const wallet = new MeshWallet({
  networkId: 0,
  fetcher: blockchainProvider,
  submitter: blockchainProvider,
  key: {
    type: 'root',
    bech32: fs.readFileSync('seller.skey').toString().trim()
  }
})

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

// The `AuctionDatum` to be stored in the output.
const datumOut = {
  alternative: 1, // Corresponds to `Nothing`
  fields: []
}

// The token we are minting
const token = {
  assetName: 'TokenToBeAuctioned',
  assetQuantity: '1',
  recipient: {
    address: auctionValidatorAddress,
    datum: { value: datumOut, inline: true }
  }
}

const walletAddress = (await wallet.getUsedAddresses())[0]

// The redeemer for the minting policy, corresponding to `()`.
const redeemer = {
  data: {
    alternative: 0,
    fields: []
  }
}

const tx = new Transaction({ initiator: wallet })
tx.mintAsset(mintingPolicy, token, redeemer)
const unsignedTx = await tx.setRequiredSigners([walletAddress]).build()
const signedTx = await wallet.signTx(unsignedTx)
const txHash = await wallet.submitTx(signedTx)

console.log(
  `Minted a token at address ${auctionValidatorAddress}. Tx hash: ${txHash}`
)
