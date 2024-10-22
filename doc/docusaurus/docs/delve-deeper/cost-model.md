---
sidebar_position: 15
---

# Cost Model

The cost model is used to determine the portion of the transaction fee that accounts for Plutus script execution.
It assigns execution units, consisting of a CPU component and a memory component, to the execution of a Plutus script, which is then used to calculate the corresponding fee in Ada.

Cardano is designed for determinism.
The script execution fee, and indeed the entire transaction fee, can be accurately predicted off-chain before the transaction is submitted.
Unlike some other blockchains, there's no risk of a script incurring higher costs on-chain than expected.
On Cardano, the fee calculated when running the script locally is the exact fee charged on-chain[^1].

To learn more about the cost model, take a look at [An overview of the Plutus Core cost model](https://github.com/IntersectMBO/plutus/blob/master/doc/cost-model-overview/cost-model-overview.pdf).

---

[^1]: A transaction may of course be rejected for reasons such as some input UTXOs no longer exist, in which case the script won't be executed.
If the script is executed, the fee will be exactly as predicted.
