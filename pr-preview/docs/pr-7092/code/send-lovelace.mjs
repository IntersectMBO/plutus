import { BlockfrostProvider, MeshWallet, Transaction } from '@meshsdk/core'

import fs from 'node:fs'

const blockfrostKey = 'Replace with Blockfrost Project ID'
const blockchainProvider = new BlockfrostProvider(blockfrostKey)

const recipient = fs.readFileSync(`${process.argv[2]}.addr`).toString()

const wallet = new MeshWallet({
  networkId: 0,
  fetcher: blockchainProvider,
  submitter: blockchainProvider,
  key: {
    type: 'root',
    bech32: fs.readFileSync('seller.skey').toString().trim()
  }
})

// Send 1000 Ada
const unsignedTx = await new Transaction({ initiator: wallet })
  .sendLovelace(recipient, '1000000000')
  .build()

const signedTx = await wallet.signTx(unsignedTx)

const txHash = await wallet.submitTx(signedTx)

console.log(`1000 Ada sent. Recipient: ${recipient}, Tx hash: ${txHash}`)
