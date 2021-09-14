.. _what_is_cost_model:

What is the Plutus cost model?
==============================

Validating a transaction with Plutus scripts requires stake pool operators to spend time and memory on running programs that were authored by untrusted parties.
The Plutus cost model ensures that node operators are adequately compensated with transaction fees for the resources they spend on running Plutus scripts.
The cost model rests on two pillars.

1. Measuring the cost of Plutus scripts in abstract execution units
2. Translating execution units to Ada

Measuring the ExBudget
----------------------

The :hsobj:`PlutusCore.Evaluation.Machine.ExBudget.ExBudget` type records the resources that are need to run :term:`Plutus Core` scripts.
The budget consists of two fields: :hsobj:`PlutusCore.Evaluation.Machine.ExBudget.exBudgetCPU` for CPU time and :hsobj:`PlutusCore.Evaluation.Machine.ExBudget.exBudgetMemory` for RAM allocated.

CPU time is measured in Picoseconds and memory is measured in machine words.
The exact amount of CPU steps and memory used by a Plutus script invocation depends on the transaction that it runs in, not least because the :hsobj:`Plutus.V1.Ledger.Contexts.ScriptContext` argument that the script receives is a Plutus representation of that transaction.
At the same time, the ExBudget requirements are known precisely at the time the transaction is constructed.
This means that we can tell exactly how much CPU and RAM will be used by the node to validate a particular Plutus script input, and don't overpay for resources.

.. note::

    This property of Plutus scripts is sometimes called *determinism* or *deterministic cost*.

When running a Plutus app, the budget of any Plutus scripts that are used to unlock transaction outputs is measured, and paid for, by the wallet that's balancing the spending transaction.
The Plutus libraries offer two functions for computing 'ExBudget's during development:

1. :hsobj:`Plutus.Trace.Emulator.Extract.writeScriptsTo` for building realistic transactions in a simulated environment. See :ref:`analysing_scripts` for details.
2. :hsobj:`Plutus.V1.Ledger.Scripts.evaluateScript`, a lower-level API for evaluating individual Plutus scripts. Note that this should be run on scripts that are fully applied to all their arguments (otherwise you will only measure a partial evaluation)

Paying for the ExBudget
-----------------------

Once the abstract cost of a script invocation has been determined in the form of an `ExBudget`, this budget needs to be translated to Ada and added to the transaction fees.

The price of a unit of CPU time or RAM is set in the protocol parameters of the network.
Like the other protocol parameters it can be adjusted over time, if a proposal to change it reaches consensus.

The reason for splitting the cost model into two parts is that this allows the Ada price of scripts to be changed without a change to the Plutus language itself.

Further reading
---------------

* The `[Budgeting]` note in `PlutusCore.Evaluation.Machine.ExBudget.hs` explains the budgeting process in some more detail