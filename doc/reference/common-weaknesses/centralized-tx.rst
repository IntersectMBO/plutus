Centralized Transaction Processing Attack
=========================================

Any centralized transaction processing service represents a single point of failure that could allow for a denial of service attack or simply be overwhelmed during a period of high user load.

Risks
~~~~~

A selective denial of service attack on a centralized processing resource could allow an attacker to crowd out legitimate users. An example is for an auction contract with a deadline where the attacker secures a winning low bit and then blocks follow on bids by attacking the bid processing server.

Solutions
~~~~~~~~~

This can be mitigated in different ways by focusing on either protecting the centralized server from DoS attacks or by using a contract architecture that is immune to the attack.

Server DoS mitigation would use well known network attack prevention and cloud based scaling techniques to load ballance the centralized request processing to ensure that it can remain availible during an attack.

Alternatively, the contract architecture may be designed in a way that doesnt rely on sequential processing of the contract via a centralized server. In an example auction contract the sequential architecture might carry state representing the highest bid and every user bid must interact with the contract and update its state. This version serializes the bid checking logic and is subject to this type of attack. In contrast, a parallel version where bids are published independantly with individual UTxOs and processed as a batch after the auction ends. Assuming users have a way of submitting transactions through a local node the parallel architecture avoids the central point of failure that allows for DoS attacks.
