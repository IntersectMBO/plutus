.. highlight:: haskell
.. _analysing_scripts:

How to analyse the cost and size of Plutus scripts
==================================================

Running Plutus scripts on a validating node uses CPU time and RAM space, which are paid for by transaction fees.
When building a decentralised application in Plutus we need to keep an eye on the size of the transactions that we submit to the network.

The Plutus libraries give us some tools for measuring the resource consumption of our scripts.

Resource use of Plutus scripts
------------------------------

There are two types of resources used by Plutus transactions.
First we have the runtime cost -- the amount of CPU and RAM used to actually run the script.
Then there is the network cost -- the size of the transaction, which determines network load and storage need when the transaction is added to the blockchain.

The `Plutus.Trace.Emulator.Extract` module lets us analyse both types of cost for transactions that are produced by the Plutus :term:`emulator`.

:hsobj:`Plutus.Trace.Emulator.Extract.writeScriptsTo` is a function that, given an emulator trace, produces a JSON file for each transaction that is created during that trace.

.. literalinclude:: ./WriteScriptsTo.hs
   :start-after: BLOCK0
   :end-before: BLOCK1

The :hsobj:`Plutus.Trace.Emulator.Extract.Command` argument selects one of two modes of :hsobj:`Plutus.Trace.Emulator.Extract.writeScriptsTo`.
The mode determines what kind of data is written to the folder specified in :hsobj:`Plutus.Trace.Emulator.Extract.scPath`.

1. :hsobj:`Plutus.Trace.Emulator.Extract.Scripts` writes the validator scripts, one for each script input that is validated as part of the emulator trace. Here we have the choice between fully applied validators and unapplied validators. *Fully applied* means that we get a :term:`Plutus Core` (PLC) program that can be evaluated to the unit value (or an error). This is the program that the node actually runs when validating the script input, and it is used for determining the script execution cost. *Unapplied* results in the PLC program of the unapplied validator. This tells us the size of the serialised Plutus script that we need to attach to the spending transaction. In both cases the CPU and memory budget in ExUnits will be displayed in the terminal (see sample output below).
2. :hsobj:`Plutus.Trace.Emulator.Extract.Transactions` writes all partial transactions that are sent to the (emulated) wallet for balancing before they are submitted to the network. Each partial transaction results in a JSON file. The `transaction` field of the JSON object contains the actual transaction in the text envelope format used by `cardano-api`. Since the transaction body is hex encoded, we can look at the length of the `cborHex` field and divide it by two in order to get the size of the partial transaction in bytes. Note that the final transaction will be slightly larger, because some additional inputs and outputs will be added by the wallet.

Examples
--------

To see :hsobj:`Plutus.Trace.Emulator.Extract.writeScriptsTo` in action you can run the `plutus-use-cases-scripts` command that is part of the `plutus-use-cases` package in our repository.

Validator scripts
~~~~~~~~~~~~~~~~~

.. code-block:: shell

    cabal run plutus-use-cases-scripts -- ./tmp scripts

results in the following output:

.. code-block:: shell

    Writing scripts (fully applied) to: ./tmp
    Writing script: ./tmp/auction_1-1.flat (Size: 3.7kB, Cost: ExCPU 309803992, ExMemory 789488)
    Writing script: ./tmp/auction_1-2.flat (Size: 9.1kB, Cost: ExCPU 1122022080, ExMemory 3410856)
    Writing script: ./tmp/auction_1-3.flat (Size: 9.1kB, Cost: ExCPU 1126876612, ExMemory 3408894)
    Writing script: ./tmp/auction_1-4.flat (Size: 3.9kB, Cost: ExCPU 395045625, ExMemory 989992)
    Writing script: ./tmp/auction_2-1.flat (Size: 3.7kB, Cost: ExCPU 309803992, ExMemory 789488)
    Writing script: ./tmp/auction_2-2.flat (Size: 9.1kB, Cost: ExCPU 1122022080, ExMemory 3410856)
    Writing script: ./tmp/auction_2-3.flat (Size: 9.2kB, Cost: ExCPU 1267324633, ExMemory 3853688)
    Writing script: ./tmp/auction_2-4.flat (Size: 9.4kB, Cost: ExCPU 1376566955, ExMemory 4153874)
    Writing script: ./tmp/auction_2-5.flat (Size: 9.1kB, Cost: ExCPU 1126876612, ExMemory 3408894)

.. note::
    The program writes out fully applied validators by default. Fully applied validators are larger than unapplied validators because they contain not just the validator code itself but also all arguments, including the :hsobj:`Plutus.V1.Ledger.Contexts.ScriptContext`. The script context can be quite large as it is a representation of the entire transaction body.

Running the program in the unapplied validator mode gives us a more realistic picture:


.. code-block:: shell

    cabal run plutus-use-cases-scripts -- ./tmp scripts --unapplied-validators
    Writing scripts (unapplied) to: ./tmp
    Writing script: ./tmp/auction_1-1-unapplied.flat (Size: 2.9kB, Cost: ExCPU 309803992, ExMemory 789488)
    Writing script: ./tmp/auction_1-2-unapplied.flat (Size: 8.1kB, Cost: ExCPU 1122022080, ExMemory 3410856)
    Writing script: ./tmp/auction_1-3-unapplied.flat (Size: 8.1kB, Cost: ExCPU 1126876612, ExMemory 3408894)
    Writing script: ./tmp/auction_1-4-unapplied.flat (Size: 2.9kB, Cost: ExCPU 395045625, ExMemory 989992)
    Writing script: ./tmp/auction_2-1-unapplied.flat (Size: 2.9kB, Cost: ExCPU 309803992, ExMemory 789488)
    Writing script: ./tmp/auction_2-2-unapplied.flat (Size: 8.1kB, Cost: ExCPU 1122022080, ExMemory 3410856)
    Writing script: ./tmp/auction_2-3-unapplied.flat (Size: 8.1kB, Cost: ExCPU 1267324633, ExMemory 3853688)
    Writing script: ./tmp/auction_2-4-unapplied.flat (Size: 8.1kB, Cost: ExCPU 1376566955, ExMemory 4153874)
    Writing script: ./tmp/auction_2-5-unapplied.flat (Size: 8.1kB, Cost: ExCPU 1126876612, ExMemory 3408894)
    (...)

Now the script sizes are more realistic.

Partial transactions
~~~~~~~~~~~~~~~~~~~~

.. code-block:: shell
    
    cabal run plutus-use-cases-scripts -- ./tmp transactions -p ./plutus-use-cases/scripts/protocol-parameters.json

results in

.. code-block:: shell

    Writing transactions to: ./tmp
    Writing partial transaction JSON: ./tmp/auction_1-1.json
    Writing partial transaction JSON: ./tmp/auction_1-2.json
    Writing partial transaction JSON: ./tmp/auction_1-3.json
    Writing partial transaction JSON: ./tmp/auction_1-4.json
    Writing partial transaction JSON: ./tmp/auction_2-1.json
    Writing partial transaction JSON: ./tmp/auction_2-2.json
    Writing partial transaction JSON: ./tmp/auction_2-3.json
    (...)

Each file contains the partial transaction and some additional information that the wallet uses for balancing.

.. code-block:: json

    {
        "transaction": {
            "cborHex": "84a500800d800(...)",
            "description": "",
            "type": "Tx AlonzoEra"
        },
        "signatories": [],
        "inputs": [
            {
                "txIn": "0636250aef275497b4f3807d661a299e34e53e5ad3bc1110e43d1f3420bc8fae#6",
                "txOut": {
                    "address": "addr1vy6aahffs2sreuu70h8q8jpen98lmmpwc6cy788j6s8xrgcpajqhn",
                    "value": {
                        "lovelace": 100000000
                    }
                }
            }
        ]
    }
