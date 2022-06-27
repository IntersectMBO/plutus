.. _what_is_the_plutus_platform:

What is the Plutus Platform?
============================

The Plutus Platform is a platform for writing *applications* that interact with a *distributed ledger* featuring *scripting* capabilities, in particular the :term:`Cardano` blockchain.

Applications
------------

What sort of "applications" are we talking about here?
Let's think about a pair of users, Alice and Bob, who want to engage in an atomic swap of some assets stored on Cardano.

.. uml::
   :caption: Alice and Bob doing an atomic swap

   actor Alice
   actor Bob
   participant Application
   database Cardano

   Alice -> Application: I want to do an escrowed swap with Bob,\n 50 Ada for my Special Token
   Application -> Ledger: I want to lock up Alice's Special Token so that\n it can only be unlocked if Bob completes the swap
   Ledger -> Application: Ok, that change has settled
   Application -> Bob: Hey, Alice wants to do a swap with you
   Bob -> Application: I want to take up Alice's swap
   Application -> Cardano: I want to spend that locked output with Alice's\n Special Token while sending 50 of Bob's Ada to Alice
   Ledger -> Ledger: Does this transaction satisfy the \nconditions that were asked for? Yes it does!
   Ledger -> Application: Ok, that change has settled
   Application -> Alice: The swap is completed!
   Application -> Bob: The swap is completed!

Alice and Bob don't interact directly, nor do they directly interact with the ledger.
Very few "smart" blockchain systems encourage their users to interact directly with the chain themselves, since this is usually complex and error-prone.
Rather, the users interact with some *application* that presents the world in a form that they can understand and interact with.

Of course, such an application must want to do something with the ledger, otherwise you wouldn't need anything new!
Simple applications might do nothing more than submit basic transactions that transfer assets - imagine a simple "regular payments" application.
However, our main focus is applications that *do* use smart features in order to have a kernel of trusted code that is validated as part of the ledger.

This enables applications that are not possible otherwise.
Alice and Bob need trusted logic in order to perform their swap: a "dumb" application could submit the transactions transferring the assets, but would have no recourse against Bob defecting.
Using the smart features of the ledger ensures that Bob can't take Alice's token unless he *really does* send her the money, and it does this without involving a trusted third party.

Creating and using the trusted kernel of code is the most technically difficult and security-sensitive part of the whole operation.
Nonetheless, writing the rest of the application contains plenty of complexity.
Amongst other things, an application needs to deal with the software around the ledger (wallets, nodes, etc.); distributed systems issues such as settlement delays, inconsistent state between parties, and rollbacks; and simple user-experience issues like upgrades, state management and synchronization.
Furthermore, while none of these are quite as security-critical as the trusted kernel, users certainly *can* be attacked through such applications, and even non-malicious bugs are likely to be quite upsetting when a user's money is at stake.

Even simple applications must deal with this complexity, and for more advanced applications that deal with state across time, the difficulty is magnified.

The Plutus Platform
-------------------

This is why the Plutus Platform is a *platform*.
Rather than just providing a few tools to make the bare minimum possible, we aim to support application development in its entirety, right the way through from authoring to testing, runtime support, and (eventually) verification.
Ultimately, we wrote it because we needed it ourselves to do anything useful!

Conceptually, the Platform breaks down based on which part of the system we're interested in:

- :ref:`Plutus Foundation<what_is_plutus_foundation>`: support for writing the trusted kernel of code, and executing it on the chain
- `The Plutus Application Framework <https://github.com/input-output-hk/plutus-apps>`_: support for writing applications ("Plutus Applications") in a particular style

.. figure:: ./platform-architecture.png

    A high-level architecture of the Plutus Platform, with an emphasis on applications.

Further reading
---------------

The platform is introduced in :cite:t:`plutus-platform-summit`.

The design of the platform is discussed in :cite:t:`plutus-report`.
