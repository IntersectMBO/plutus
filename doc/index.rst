Plutus Core and Plutus Tx user guide
==================================================

Plutus Core
---------------------

The Plutus project consists of Plutus Core, the programming language used for 
scripts on Cardano; tooling and compilers for compiling various intermediate 
languages into Plutus Core; and Plutus Tx, the compiler that compiles the Haskell 
source code into Plutus Core to form the on-chain part of a contract application. 
All of this is used in combination to write Plutus Core scripts that run on the 
Cardano blockchain. The Cardano ledger is able to interact with compiled Plutus Core 
scripts through the ledger interface. 

This documentation introduces the Plutus Core programming language and programming 
with Plutus Tx. It is meant to be educational, so it includes explanations, tutorials 
and how-to instructions. 

The intended audience of this documentation includes people who want to implement 
smart contracts on the Cardano blockchain. This involves using Plutus Tx to write 
scripts, requiring some knowledge of the Haskell programming language. 

This guide is also meant for certification companies, certification auditors, 
and people who need to reference specifications. See, for example: 

* the `Cardano Ledger Specification <https://github.com/input-output-hk/cardano-ledger#cardano-ledger>`_ and 
* the `Plutus Core Specification <https://github.com/input-output-hk/plutus#specifications-and-design>`_. 

The Plutus repository
----------------------------------

The `Plutus repository <https://github.com/input-output-hk/plutus>`_ contains 
the implementation, specification, and mechanized metatheory of Plutus Core. 
It also contains the Plutus Tx compiler and the libraries, such as ``PlutusTx.List``, 
for writing Haskell code that can be compiled to Plutus Core. 

Public Plutus libraries documentation
-------------------------------------------

See also the `public Plutus libraries documentation <https://playground.plutus.iohkdev.io/doc/haddock/>`_ 
to access Haddock-generated documentation of all the code. 


.. toctree::
   :caption: Explore Plutus
   :maxdepth: 2

   explanations/index
   tutorials/index
   howtos/index
   troubleshooting

.. toctree::
   :caption: Architectural decision records
   :maxdepth: 1

   adr/index

.. toctree::
   :caption: Reference
   :maxdepth: 2

   reference/index
