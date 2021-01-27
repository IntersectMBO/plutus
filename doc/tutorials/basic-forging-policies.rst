.. highlight:: haskell
.. _basic_forging_policies_tutorial:

Writing basic forging policies
==============================

:term:`Forging policy scripts<forging policy script>` are the programs that can be used to control the forging of new assets on the chain.
Forging policy scripts are much like :term:`validator scripts<validator script>`, and they are written similarly, so check out the `validator script tutorial <basic_validators_tutorial>`_ before reading this one .

Forging policy arguments
------------------------

Forging policies, like validators, receive some information from the validating node:

..
    TODO: redeemers for policies aren't currently implemented in the mock version!

- The :term:`redeemer`, which is some script-specific data specified by the party performing the forging.
- The :term:`forging context`, which contains a representation of the spending transaction, as well as the hash of the forging policy which is currently being run.

The forging policy is a function which receives these two inputs as *arguments*.
The validating node is responsible for passing them in and running the forging policy.
As with validator scripts, the arguments are passed encoded as :hsobj:`Language.PlutusTx.Data.Data`.

Using the forging context
-------------------------

..
    TODO: pin down the naming: forging vs policy context

Validators have access to the :term:`forging context` as their second argument.
This will always be a value of type ``Ledger.Validation.PolicyCtx`` encoded as ``Data``.

The forging context is very similar to the :term:`validation context`, and allows access to all the same features of the transaction.
Forging policies tend to be particularly interested in the ``forge`` field, since the point of a forging policy is to control which tokens are forged.

It is also important for a forging policy to look at the tokens in the ``forge`` field that are part of its own asset group.
This requires the policy to refer to its own hash -- fortunately this is provided for us in the forging context.

Here is an example that puts this together to make a simple policy that allows anyone to forge the token so long as they do it one token at a time.

.. literalinclude:: BasicPolicies.hs
   :start-after: BLOCK1
   :end-before: BLOCK2

Probably the simplest useful policy is one that requires a specific key to have signed the transaction in order to do any forging.
This gives the key holder total control over the supply, but this is often sufficient for asset types where there is a centralized authority.

.. literalinclude:: BasicPolicies.hs
   :start-after: BLOCK2
   :end-before: BLOCK3

.. note::
   We don't need to check that this transaction actually forges any of our asset type: the ledger rules ensure that the forging policy will only be run if some of that asset is being forged.
