Plutus Programming and Reference Guide
=============================================

About Plutus
--------------------

Plutus is the programming language and compiler (Plutus Tx) that is used to write 
Plutus scripts that run on the Cardano blockchain. Plutus Tx is the compiler plugin 
for writing Plutus Core programs in Haskell. Compiled Plutus Core programs are able to 
interact with the Cardano ledger through the ledger interface. 

About This Documentation
---------------------------------

The purpose of this documentation is to serve as an introduction to the Plutus language 
and to programming in Plutus. It is also meant to be educational, so it includes tutorials 
and how-to instructions. It may also serve as a reference for beginning and experienced 
developers. 

Intended Audience
---------------------------

The intended audience of this documentation is DApp developers, Plutus developers, 
developers writing smart contracts, Haskell developers who want to write Plutus scripts, 
and developers who want to learn to use the compiler Plutus Tx. 

It is also intended for developers who want to learn Plutus from the definitive 
source: the team that developed the Plutus language, which is built on top of Haskell. 

While it is helpful to have a background in Haskell, this document is also intended 
for developers who may not know Haskell very well. 

This document is also intended for people who need to reference and access specifications, 
along with certification companies, certification auditors, and anyone doing certification 
and auditing. 

The Plutus Core Repository
----------------------------------

The `Plutus Core Repository <https://github.com/input-output-hk/plutus>`_ contains 
the implementation, specification, and mechanized metatheory of Plutus Core. 
It contains Plutus Tx, the compiler from Haskell source code to Plutus Core. 
Plutus Tx takes the Haskell source code and compiles it into PLC Plutus Core. 


.. toctree::
   :caption: Explore Plutus
   :maxdepth: 2

   explanations/index
   tutorials/index
   howtos/index
   troubleshooting

.. toctree::
   :caption: Architecture design records
   :maxdepth: 1

   adr/index

.. toctree::
   :caption: Reference
   :maxdepth: 2

   reference/index
