.. highlight:: haskell
.. _basic_apps_tutorial:

Writing basic Plutus apps in the Plutus Playground
==================================================

:term:`Plutus apps<contract application>` are programs that run off-chain and manage active contract instances.
They monitor the blockchain, ask for user input, and submit transactions to the blockchain.
If you are a contract author, writing a Plutus app is the easiest way to create and spend Plutus script outputs.

The Contract Monad
------------------

Plutus apps use the :hsobj:`Language.Plutus.Contract.Contract` monad.
``Contract`` encapsulates effects that are useful for managing contract instances.
A simple contract is one that prints a log message and then exits.

.. literalinclude:: BasicApps.hs
   :start-after: BLOCK1
   :end-before: BLOCK2

.. When `running this app in the Plutus playground <plutus-playground>` we get the following log:
.. TODO: Insert log

We can ask the user for input at any time while the app is running.
To achieve this we first need to tell the compiler about the type of data that we expect the user to provide.
This is what the contract's :term:`schema` does: It describes all :term.`endpoints <endpoint>` that the contract may use.
The schema is defined as a Haskell type.
We can build a schema using the ``Endpoint`` type family to construct individual endpoint types, and the ``.\/`` operator to combine them.

.. literalinclude:: BasicApps.hs
   :start-after: BLOCK2
   :end-before: BLOCK3

..
      TODO: How can I link to types from the prelude (such as Data.String.String)?

The ``DemoSchema`` type defined above has a single endpoint called "name", which expects a ``String``.

