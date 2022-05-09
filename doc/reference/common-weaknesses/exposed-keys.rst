Passwords or Keys may be exposed on the blockchain
==================================================

If information which is supposed to remain private, such as a password for example, is stored in UTXO data or redeemers, then it may be read by anyone with access to the transaction pool or the blockchain. When secret data is embedded in larger data structures, then it is easy to forget which values may contain secrets, and thus to leak them inadvertently.

Risks
~~~~~

Making secrets publicly visible may allow arbitrary contract execution leading to loss of funds.

Solutions
~~~~~~~~~

Secret data must be managed carefully and only ever stored on the blockchain when it has been correctly encrypted.

