# Plutus docs revamp project

This outline shows the proposed reorganized structure for the Plutus Core Plutus Tx documentation revamp. 

# Reorganized top levels

## 1. [Introduction](010_introduction.md)
> **Status**
> 
> - Ported over existing content. 
> - Planning further reorganization and editing. 
> - Not ready for review. 

## 2. [Core concepts](020_core-concepts.md)
> **Status**
> 
> - Ported over existing content. 
> - Planning further reorganization and editing. 
> - Not ready for review. 

- The Plutus Platform
   - Applications
   - The Plutus Platform
   - Further reading
- Ledgers
   - Account-based and UTXO-based ledgers
   - Scripts and the Extended UTXO Model
   - Different kinds of scripts
   - Further reading
- Plutus Foundation
   - Plutus Core
   - Plutus Tx
   - Further reading
- Plutus language versions

## 3. [Developer onboarding and quick setup](030_dev-onboarding-quick-setup.md)

> **Notes**
>   - Review comments incorporated as of March 26. 
>   - Ziyang's comments in [Draft PR](https://github.com/IntersectMBO/plutus/pull/5866/commits) speak to intended audience, scope, and reconsidering our example contract selection. 
>   - Take into account the [Plutus-tx-template repo](https://github.com/IntersectMBO/plutus-tx-template) and how to use it. 

- Objective
- Setting up and testing your development environment
- Testing your environment setup
- Core concepts of Plutus smart contracts
- Writing your first Plutus smart contract
- First smart contract example
   - Code example with explanations
- The larger context and next steps

## 4. [Simple example](040_simple-example.md)
> **Status**
> 
> - Ported over content. 
> - Intending to prune down and edit. 
> - Some content will probably be moved to other sections. 

- Section 4. Simple example
   - Overview
- The EUTXO model, datum, redeemer and script context
- Auction properties
- Plutus Tx code
   - Data types
   - Main validator function
- Life cycle of the auction smart contract
   - Initial UTXO
   - The first bid
   - The second bid
   - Closing the auction
- Libraries for writing Plutus Tx scripts
- Alternatives to Plutus Tx
- Off-chain code
- Further reading
   - The EUTXO model

## 5. [Using Plutus Tx](050_using-plutus-tx.md)
> **Status**
> 
> - Ported over existing content as of March 29 into new org structure. 
> - Code block includes are not yet functional. Working with web dev team to figure out how we will handle this if we discontinue using .rst files and migrate to Docusaurus and .md files. 
> - Proposed new organizational structure for this section is reflected below. The file [050.1_proposed-edits_using-plutus-tx.md](050.1_proposed-edits_using-plutus-tx.md) is a draft in progress as a basis for discussion and for gathering more information from the Plutus team.

> NOTE: Paragraph numbering is being used temporarily to help with organizing and editing content. 

1. High-level overview of how Plutus Tx works
   1.1 Key technique for implementing Plutus tx: staged metaprogramming

2. Basic syntax and structure of a Plutus Tx program
   2.1 Plutus-Tx-Template repo
   2.2 Template Haskell preliminaries
   2.3 Simple pattern
   2.4 Quotes
   2.5 Splicing quotes

3. Writing Plutus Tx Programs
   3.1 Plutus Tx standard usage pattern (how all of our Plutus Tx programs are written)
   3.2 Functions and datatypes
   3.3 Typeclasses
   3.4 The Plutus Tx Prelude
   3.5 Plutus Tx Prelude has redefined versions of many standard typeclasses
   3.6 Lifting values for generating code dynamically

4. Compiling Plutus Tx, describing the Plutus Tx compilation process

   4.1 GHC Extensions, Flags and Pragmas
      4.1.1 Extensions
      4.1.2 Flags
      4.1.3 Pragmas
   4.2 Reference: Plutus Tx Compiler Options

5. Troubleshooting and Debugging
   5.1 Common errors and how to fix them
   5.2 Debugging techniques for Plutus Tx programs

6. Real-world Examples and Use Cases
   6.1 Practical applications of Plutus Tx
   6.2 Case studies and code examples

## 6. [Working with scripts](060_working-with-scripts.md)
> **Status**
> 
> - Ported over existing content into new org structure. 
> - Code block includes are not yet functional. Working with web dev team to figure out how we will handle this if we discontinue using .rst files and migrate to Docusaurus and .md files. 
> - Not ready for review -- more editing planned. 

- Writing basic validator scripts
   - Validator arguments
   - The Data type
   - Signaling failure
   - Validator functions
   - Plutus script context versions
- Writing basic minting policies
   - Minting policy arguments
   - Plutus script context versions
   - Writing minting policies
   - Other policy examples
- Creating and submitting transactions using an off-chain framework
- Libraries for writing Plutus Tx scripts
- **Using AsData to optimize scripts** (advanced topic)
- Exporting scripts, datums and redeemers
- Profiling the budget usage of Plutus scripts
   - Compiling a script for profiling
   - Acquiring an executable script
   - Running the script
   - Analyzing the results

## 7. [Working with Plutus Core](070_working-with-plutus-core.md)

> **Status**
> 
> First draft outline for review and feedback. 
> The scope of this draft may encompass more than is needed for our docs. 

- Introduction to Plutus Core
- Plutus Core Syntax and Semantics
   - The basic constructs of Plutus Core, such as variables, functions, and applications, as well as the type system that includes types and kinds
   - Syntax and semantics of Plutus Core
   - Understanding data types used in Plutus Core and how they relate to the types in Haskell
- Compilation Process
   - Understanding how high-level Plutus Tx code is compiled down to Plutus Core, including the role of the Plutus compiler and the abstract syntax tree (AST)
   - Understanding the compilation target and execution environment of your Plutus Tx code
- Execution Model
   - Understanding how your contracts will execute on-chain
   - The low-level execution model of Plutus Core 
   - The cost model for computing resource usage
- Built-in Functions
   - Exploring the built-in functions and types provided by Plutus Core that are essential for contract execution.
- Formal Specification of Plutus Core
   - The formal [Plutus Core Specification](https://ci.iog.io/job/input-output-hk-plutus/master/x86_64-linux.packages.plutus-core-spec/latest/download/1) for understanding the precise behavior of the Plutus Core language.
- Security Considerations
   - The security aspects of smart contract development, including auditing Plutus Core code for safety and correctness.
- Interacting with the Extended UTXO Model (EUTXO)
   - Understanding how Plutus Core interacts with the ledger and the EUTXO model specific to Cardano.
- Advanced Topics
   - Optimizations, bytecode generation, and other advanced features of Plutus Core for those who want to understand the language at a deeper level.
- Tools and Resources
   - The tools available for Plutus Core development, such as decompilers, pretty-printers, and debuggers.
   - Troubleshooting

## 8. [Architectural decision records](080_adr-index.md)

## 8a. [ADR 1](081_adr1.md)

## 8b. [ADR 2](082_adr2.md)

## 8c. [ADR 3](083_adr3.md)

## 8d. [ADR 4](084_adr4.md)

## 9. [Reference](090_reference.md)
> **Status**
> 
> - Ported over content. 
> - Not ready for review. 
> - I expect to break this section into multiple pages once we have our docs platform available to use. It is admittedly pretty long right now, but useful to see it all in one file for this stage. 

- Writing scripts
   - Plutus Tx Compiler Options
   - Optimization techniques for Plutus scripts
      - Identifying problem areas
      - Using strict let-bindings to avoid recomputation
      - Specializing higher-order functions
      - Common sub-expression elimination
      - Using `error` for faster failure
   - Examples
   - Common weaknesses
      - Double satisfaction
         - What is going wrong here?
         - Risks
         - Solutions
            - Unique outputs
            - Ban other scripts
      - Hard limits
         - Risks
         - Solutions
            - Careful testing
            - Bounding data usage
            - Providing datums when creating outputs
            - Reducing script size costs through reference inputs
- Plutus on Cardano
   - Plutus language changes
      - Language versions
         - Plutus V1
         - Plutus V2
      - Examples
      - Built-in functions and types
         - Alonzo
         - Vasil
         - PlutusV3
         - Sums of products
         - New cryptographic primitives
         - Bitwise primitives
  - Upgrading to Vasil and Plutus script addresses
      - A Plutus V2 script will not have the same hash value as a Plutus V1 script
      - A Plutus V1 script will not necessarily have the same hash value when recompiled with a later version of the Plutus Compiler
      - When to export and save the output of a compiled script
  - Cost model parameters (Need to investigate how to migrate this content)
- Glossary

## 10. [Troubleshooting](100_troubleshooting.md)
> **Status**
> 
> - Ported over content. 
> - Not ready for review. 

- Plugin errors
   - Haddock
   - Non-`INLINABLE` functions
- Haskell Language Server issues
   - Wrong version
- Error codes
   - Ledger errors
   - Prelude errors
   - State machine errors
   - Currency errors

## 11. [FAQ](110_faq.md)
- Draft list of questions in place. Changes to the questions are pending. 
