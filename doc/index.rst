Plutus Programming and Reference Guide
=============================================

About Plutus
--------------------

The Plutus project consists of Plutus Core, the programming language used for scripts on Cardano; tooling and compilers for compiling various intermediate languages into Plutus Core;
and Plutus Tx, the compiler that compiles the Haskell source code into Plutus Core 
to form the on-chain part of a contract application. All of this is used in combination 
to write Plutus Core scripts that run on the Cardano blockchain. Compiled Plutus Core 
scripts are able to interact with the Cardano ledger through the 
ledger interface. 

The Plutus Core Repository
----------------------------------

The `Plutus Core Repository <https://github.com/input-output-hk/plutus>`_ contains 
the implementation, specification, and mechanized metatheory of Plutus Core. 
It also contains Plutus Tx. 

About This Documentation
---------------------------------

The purpose of this documentation is to serve as an introduction to the Plutus language 
and to programming in Plutus. It is meant to be educational, so it includes explanations, 
tutorials and how-to instructions. It is also intended as a reference for beginning and 
experienced developers. 

Intended Audience
---------------------------

The intended audience of this documentation includes DApp developers, Plutus developers, 
developers writing smart contracts, Haskell developers who want to write Plutus scripts, 
and developers who want to learn to use the compiler, Plutus Tx. It is also designed for 
developers who want to learn Plutus directly from the team that developed the Plutus language. 

Because Plutus is built on top of Haskell, it is helpful to have a background in Haskell. 
However, this document is also intended for developers who may not know Haskell very well. 

This guide is also meant for people who need to reference and access specifications, 
as well as for certification companies and certification auditors. 


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
