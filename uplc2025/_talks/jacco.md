---
name: A Layered Certifying Compiler Architecture
speakers:
  - Jacco Krijnen
categories:
  - Talk
---
The formal verification of an optimising compiler for a realistic programming language is no small task. Most verification efforts develop the compiler and its correctness proof hand in hand.
Unfortunately, this approach is less suitable for today’s constantly evolving community-developed open-source compilers and languages.
I will discuss an alternative approach to high-assurance compilers, where a separate certifier uses translation validation to assess and certify the correctness of each individual compiler run.
I will also demonstrate that an incremental, layered architecture for the certifier improves assurance step-by-step and may be developed largely independently from the constantly changing main compiler code base.
This approach to compiler correctness is practical, as witnessed by the development of a certifier for the PIR-to-PIR pipeline of the Plinth compiler in the Rocq prover.
