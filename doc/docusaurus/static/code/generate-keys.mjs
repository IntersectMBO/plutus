import { MeshWallet, deserializeAddress } from '@meshsdk/core';
import fs from 'node:fs';

// generate a new secret key
const skey = MeshWallet.brew(true);

// create a Mesh wallet with the secret key
const wallet = new MeshWallet({
  networkId: 0,
  key: {
    type: 'root',
    bech32: skey,
  },
});

// obtain the address associated with the secret key
const address = wallet.getUnusedAddresses()[0];

// derive PubKeyHash from the address
const pubKeyHash = deserializeAddress(address).pubKeyHash

// write the secret key, the address and the PubKeyHash to files
fs.writeFileSync('me.skey', skey);
fs.writeFileSync('me.addr', address);
fs.writeFileSync('me.pkh', pubKeyHash);
