import { MeshWallet, deserializeAddress } from '@meshsdk/core'
import fs from 'node:fs'

// generate a new secret key
const skey = MeshWallet.brew(true)

// create a Mesh wallet with the secret key
const wallet = new MeshWallet({
  networkId: 0,
  key: {
    type: 'root',
    bech32: skey
  }
})

// obtain the address associated with the secret key
const address = (await wallet.getUnusedAddresses())[0]

// derive PubKeyHash from the address
const pubKeyHash = deserializeAddress(address).pubKeyHash

const filename = process.argv[2]

// write the secret key, the address and the PubKeyHash to files
fs.writeFileSync(`${filename}.skey`, skey)
fs.writeFileSync(`${filename}.addr`, address)
fs.writeFileSync(`${filename}.pkh`, pubKeyHash)
