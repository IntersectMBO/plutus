---
sidebar_position: 5
---

# Generating Keys and Addresses

To start, clone the plutus-tx-template repository into the `on-chain` directory.
Then, create a separate `off-chain` directory.

```
git clone git@github.com:IntersectMBO/plutus-tx-template.git on-chain
mkdir off-chain
```

We recommend using the Nix shell that comes with `plutus-tx-template` to run this example.
The Nix shell provides the correct versions of all dependencies, including GHC, Cabal, Node.js, and various C libraries.
To enter the nix shell, run

```
nix develop on-chain/
```

The first run of `nix develop` may take some time so please be patient.

We'll use [mesh](https://meshjs.dev/), a JavaScript framework, for writing off-chain code.
We'll use [Blockfrost](https://blockfrost.io/) as the blockchain provider, to avoid the need of running a local node.

The first step is to generate keys and addresses for the seller and the bidders.
Add a new file named `off-chain/generate-keys.mjs`, with the following content:

<LiteralInclude file="generate-keys.mjs" language="javascript" title="generate-keys.mjs" />

Then, generate keys and addresses for one seller and two bidders by running:

```
node generate-keys.mjs seller
node generate-keys.mjs bidder1
node generate-keys.mjs bidder2
```

This will create three files for each participant (seller, bidder1, and bidder2): a `.skey` file that contains a secret key, a `.addr` file that contains the corresponding wallet address, and a `.pkh` file that contains the corresponding public key hash.
