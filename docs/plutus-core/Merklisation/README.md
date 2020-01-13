# plutus-merklisation

This directory contains the results of some experiments involving type erasure
and Merklisation for Plutus Core abstract syntax trees.

  * [PLC-AST-types.md](./PLC-AST-types.md): an overview of the types used to represent Plutus Core asbtract syntax trees
  * [AST-analysis.md](./AST-analysis.md): Some basic statistics for validator ASTs for our use cases.

  * [Erasure.md](./Erasure.md): Statistics and comments on type
    erasure in PLC ASTs for validator code from our use cases.

  * [Merklisation-notes.md](./Merklisation-notes.md): a proposal for Merklised ASTs for Plutus Core, together with
    some analysis of Merklisation of types.

  * [Merklising-programs.md](./Merklising-programs.md): an investigataion of what happens when we Merklise the validators in our sample contracts


  * [Compressibility.md](./Compressibility.md): an analysis of
    serialised ASTs, showing that the CBOR data is very sparse.  This
    probably explains why the CBOR is so compressible.

