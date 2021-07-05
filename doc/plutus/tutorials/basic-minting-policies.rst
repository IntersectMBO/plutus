.. highlight:: haskell
.. _basic_minting_policies_tutorial:

Writing basic minting policies
==============================

:term:`Minting policy scripts<minting policy script>` are the programs that can be used to control the minting of new assets on the chain.
Minting policy scripts are much like :term:`validator scripts<validator script>`, and they are written similarly, so check out the :ref:`basic validators tutorial<basic_validators_tutorial>` before reading this one .

Minting policy arguments
------------------------

Minting policies, like validators, receive some information from the validating node:

- The :term:`redeemer`, which is some script-specific data specified by the party performing the minting.
- The :term:`minting context`, which contains a representation of the spending transaction, as well as the hash of the minting policy which is currently being run.

The minting policy is a function which receives these two inputs as *arguments*.
The validating node is responsible for passing them in and running the minting policy.
As with validator scripts, the arguments are passed encoded as :hsobj:`PlutusCore.Data.Data`.

Using the minting context
-------------------------

..
    TODO: pin down the naming: minting vs policy context

Validators have access to the :term:`minting context` as their second argument.
This will always be a value of type ``Ledger.Validation.PolicyCtx`` encoded as ``Data``.

The minting context is very similar to the :term:`validation context`, and allows access to all the same features of the transaction.
Minting policies tend to be particularly interested in the ``mint`` field, since the point of a minting policy is to control which tokens are minted.

It is also important for a minting policy to look at the tokens in the ``mint`` field that are part of its own asset group.
This requires the policy to refer to its own hash -- fortunately this is provided for us in the minting context.

Here is an example that puts this together to make a simple policy that allows anyone to mint the token so long as they do it one token at a time.

.. literalinclude:: BasicPolicies.hs
   :start-after: BLOCK1
   :end-before: BLOCK2

Probably the simplest useful policy is one that requires a specific key to have signed the transaction in order to do any minting.
This gives the key holder total control over the supply, but this is often sufficient for asset types where there is a centralized authority.

.. literalinclude:: BasicPolicies.hs
   :start-after: BLOCK2
   :end-before: BLOCK3

.. note::
   We don't need to check that this transaction actually mints any of our asset type: the ledger rules ensure that the minting policy will only be run if some of that asset is being minted.
