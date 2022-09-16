.. _what_is_a_ledger:

What is a ledger?
=================

The :ref:`Plutus Platform<what_is_the_plutus_platform>` is designed to work with 
distributed ledgers (henceforth simply “ledgers”). Ledgers are typically *implemented* 
with a blockchain, such as Cardano. However, much of the time when we are talking 
about ledgers we don't care about the underlying implementation, and so we will just 
talk about the ledger itself.

.. note::
    This is not always true: applications do need to care about details of how the 
    underlying blockchain works, because that affects behaviour such as settlement 
    time and rollback policies. As much as possible the Plutus Application Framework 
    tries to shield developers from this complexity, but it is not always possible.

In its simplest form, a ledger is a system that tracks who owns what.

For example:

+------------+----------+
| Owner      | Balance  |
+============+==========+
| Alice      | 43 USD   |
+------------+----------+
| Bob        | 12 USD   |
+------------+----------+

Ledgers are typically transformed by performing a *transaction* that transfers some 
assets from one party to another. In order to be *valid* a transaction will have to 
pass some checks, such as demonstrating that the transfer is authorized by the owner 
of the funds. After applying a transaction (say, Alice sends Bob 5 USD), we have a 
new state of the ledger.

+------------+----------+
| Owner      | Balance  |
+============+==========+
| Alice      | 38 USD   |
+------------+----------+
| Bob        | 17 USD   |
+------------+----------+

Account-based and UTXO-based ledgers
------------------------------------

There are two dominant paradigms for how to *represent* such a system. The first, 
account-based ledgers, model the system exactly as in our example above. They keep 
a list of accounts, and for each account, a balance. A transaction simply decreases 
the balance of the sender, and increases the balance of the recipient.

Account-based ledgers (such as Ethereum) are very simple to implement, but they 
have difficulties due to the fact that the state of an account is *global*: all 
transactions that do anything with an account must touch this one number. This can 
lead to issues with throughput, as well as ordering issues (if Alice sends 5 USD to 
Bob, and Bob sends 5 USD to Carol, this may succeed or fail depending on the order 
in which the transactions are processed).

The other paradigm is UTXO-based ledgers. UTXO-based ledgers (such as Bitcoin) 
represent the state of the ledger as a set of "unspent transaction outputs" (UTXOs).
A UTXO is like an envelope with some money in it: it is "addressed" to a particular 
party, and it contains some funds. A transaction *spends* some number of UTXOs, 
and creates some more.

So a transaction that sends 5 USD from Alice to Bob would do so by spending some 
number of already-existing UTXOs belonging to Alice, and creating a new UTXO with 
5 USD belonging to Bob.

UTXO-based ledgers are more complicated, but avoid some of the issues of account-based 
ledgers, since any transaction deals only with the inputs that it spends. Cardano 
is a UTXO-based ledger, and we heavily rely on this. For example, :term:`Hydra`, 
Cardano's scalability solution, uses the fact that independent parts of the transaction 
graph can be processed in parallel to improve throughput.

.. _scripts_and_the_eutxo_model:

Scripts and the Extended UTXO Model
-----------------------------------

UTXO-based ledgers typically start out with a very simple model of "ownership" of 
UTXOs. An output will have a public key (strictly, the hash of a public key) attached 
to it, and in order to spend this output the spending transaction must be signed by 
the corresponding private key. We call this a "pay-to-pubkey" output.

Cardano uses an extended model called the :term:`Extended UTXO Model` (EUTXO). 
In the EUTXO model, an output can be locked by (the hash of) a *script*. We call 
this a "pay-to-script" output. A script is a *program* that decides whether or not 
the transaction which spends the output is authorized to do so. Such a script is 
called a validator script, because it validates whether the spending is allowed.

A simple validator script would be one that checked whether the spending transaction 
was signed by a particular key---this would exactly replicate the behaviour of simple 
pay-to-pubkey outputs. However, with a bit of careful extension, we can use scripts 
to let us express a large amount of useful logic on the chain.

With the EUTXO model, validator scripts are passed three arguments:

- The *datum*: this is a piece of data attached to the *output* that the script is 
  locking (strictly, again, just the hash is present). This is typically used to 
  carry state.
- The *redeemer*: this is a piece of data attached to the *input* that is doing 
  the spending. This is typically used to provide an input to the script from the 
  spender.
- The *context*: this is a piece of data which represents information about the 
  transaction doing the spending. This is used to make assertions about the way 
  the output is being sent (such as "Bob signed it").

As an example, let's see how we could implement an atomic swap.

- The datum contains the keys of the two parties in the swap, and a description 
  of what they are swapping.
- The redeemer is unused.
- The context contains a representation of the transaction.

The logic of the validator script is then: does the transaction make a payment from 
the second party to the first party, containing the value that they are supposed 
to send? If so, then they may spend this output and send it where they want (or we 
could insist that they send it to their key, but we might as well let them do what 
they like with it).

Different kinds of scripts
--------------------------

The Cardano ledger currently has a few different kinds of validator scripts:

- The "simple" script language (introduced in the Allegra hard fork), which allows 
  basic checks such as time locks
- Various Plutus language versions (see :ref:`What are Plutus language versions? <what_are_plutus_language_versions>`)

Further reading
-----------------

See `The EUTXO Handbook, A deep dive into Cardano's accounting model <https://www.essentialcardano.io/article/the-eutxo-handbook>`_. 

The Extended UTXO Model is described in :cite:t:`functional-smart-contracts-summit`.
More formal detail can be found in in :cite:t:`eutxo,utxoma,eutxoma`.

For more help on how to actually implement interesting logic using the EUTXO model 
and scripts, read some of our :ref:`tutorials<plutus_tutorials>`.
