---
sidebar_position: 5
---

# Generating Keys and Addresses

The best way to setup your environment is with the [plinth-template](https://github.com/IntersectMBO/plinth-template) repository. See its [README](https://github.com/IntersectMBO/plinth-template?tab=readme-ov-file#plinth-template) for complete instructions on how to get up and running using Docker, Nix, or a custom approach.

Make sure you also have [NodeJS](https://nodejs.org/en) and [yarn](https://yarnpkg.com/) (or [npm](https://github.com/npm/cli), which comes with `NodeJS`) installed.
Then, create a separate `off-chain` directory, initialize `package.json`, and install the required dependencies:

```
git clone git@github.com:IntersectMBO/plinth-template.git on-chain
mkdir off-chain && cd $_
yarn init -y
yarn add @meshsdk/core
yarn add cbor
```

We'll use [mesh](https://meshjs.dev/), a JavaScript framework, for writing off-chain code.
We'll use [Blockfrost](https://blockfrost.io/) as the blockchain provider, to avoid the need of running a local node.
If you don't have a Blockfrost account, you can sign up for one, and create a project for the Preview network.

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
