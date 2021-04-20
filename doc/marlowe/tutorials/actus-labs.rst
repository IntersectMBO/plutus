.. _actus-labs:

Actus Labs
==========

This section gives an outline of this experimental feature, implementing
a selection of .tutorial gives an introduction to the general idea of
the Actus standard, described in the
`taxonomy <https://www.actusfrf.org/taxonomy>`_ and `technical specification <https://www.actusfrf.org/techspecs>`_.

Actus Labs allows to design, generate and analyse financial contracts
declaratively without any programming required. It has Blockly workspace
to construct contract terms. It is also planned to add analytics sidebar
with cashflows plotting and other stats.

At the moment, it supports Principal At Maturity (PAM) contract from
ACTUS standard. The essence of this contract is a bond/loan with
optional periodic interest payments.

Functionality
-------------

There are two ways to generate a contract:

-  "Generate static contract" generates simple contract with predefined
   payoffs. Such contract cannot receive data from the outside. For
   example if interest rate resets are enabled, one would need to get
   new interest rate periodically from external off-chain data source
   (Oracle) - this is only possible with "Generate reactive contract"
   button.

-  "Generate reactive contract" generates a contract with dynamically
   computed payoffs. This is achieved by embedding original payoff
   formulas into the Marlowe contract.
