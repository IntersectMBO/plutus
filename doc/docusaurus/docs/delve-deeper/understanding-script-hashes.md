---
sidebar_position: 20
---

# Understanding Script Hashes

Script hashes are a core concept and play a vital role on Cardano.
Performing an action on Cardano that involves scripts, such as spending a script UTXO or minting tokens, requires the script with a specific hash to be executed and satisfied.
The cryptographic security of script hashes makes it effectively impossible to manufacture a script that matches a given hash, ensuring the integrity of the blockchain.
A solid understanding of script hashes is essential for DApp development.

## Changing ledger language versions leads to changed script hashes

The ledger language version of a script is part of its hash, so the exact same UPLC program will have different hashes when used as a Plutus V1, V2 or V3 script.
This means, for example, you can't supply a Plutus V3 script when performing an action that requires a Plutus V1 or V2 script, as the hash won't match.

## Changing Plinth compiler versions may lead to changed script hashes

Different Plinth compiler versions may compile and optimize the same Plinth code differently, leading to different UPLC programs and, therefore, different script hashes.

Additionally, the version of GHC can affect the resulting UPLC program and script hashes.
While the Plinth compiler currently supports only one major GHC version, different minor GHC versions may lead to slightly different UPLC programs.

If you plan to use your script in the future, the best approach is to save the compiled script in a blueprint file.
For further information, refer to [Producing a Plutus contract blueprint](../working-with-scripts/producing-a-blueprint.md).

If you wish to compile your Plinth code again in the future while ensuring the script hash remains unchanged, consider using Nix to lock the versions of all dependencies by pinning to a specific version of nixpkgs.
