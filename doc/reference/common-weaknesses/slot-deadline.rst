Slot Deadline Attack
====================

In certain types of contracts with deadlines, there may be an opportunity for a kind of denial-of-service attack leading to unintended financial outcomes.

Risks
~~~~~

Any contract which carries its state via a single UTxO will be limited to a maximum of one operation per slot. For example, in the case of an auction contract in which bids can be made until a deadline, then an attacker could submit a large number of bids for the minimum acceptable bid in each slot, each of which would be accepted by the contract via a transition, and the result could be to crowd out real bids with high probability, thus winning the auction for the price of number-of-slots x transaction fee, which could be much less than the winning bid in an honest auction.

Solutions
~~~~~~~~~

To avoid this kind of vulnerability a contract must be scalable, accepting many inputs per slot—many bids per slot, in the case of an auction. For example, each bid might be made just by creating a UTXO addressed to the auction script, and the auction owner might then collect all of the submitted bids in one transaction—which would permit an arbitrary number of bids to be collected in just two slots.

