---
sidebar_position: 38
---

# Overview of Languages Compiling to UPLC

Untyped Plutus Core (UPLC) is the assembly-like language that runs in Cardano nodes for transaction validation.
The Cardano node ships with a UPLC evaluator, which is a [CEK machine](https://en.wikipedia.org/wiki/CEK_Machine).

UPLC is a low-level programming language, and is not intended to be written or modified by hand.
Besides Plutus Tx, several other high-level languages are designed to target UPLC.
These languages can be grouped into three categories:

- Standalone DSLs, which are entirely new languages
- DSLs embedded in existing general-purpose programming languages
- Subsets of existing general-purpose programming languages

These are also the three common strategies for creating DSLs in general, not limited to blockchains or Cardano.
Each strategy comes with its own benefits and drawbacks, which we'll discuss next.

## Standalone DSLs

A standalone DSL is a new language with its own syntax and semantics.
By crafting a new language from scratch, you avoid inheriting the limitations and complexities of existing languages, allowing you to tailor-make it to be as simple, intuitive and elegant as possible to program for the specific domain it targets.

On the other hand, standalone DSLs have some disadvantages.
First, designing and implementing them can be challenging.
Not only must the syntax and semantics be created from scratch, but you also need to build all necessary compiler components, tooling, and a library ecosystem from the ground up.
This can be a formidable task, as developing, testing, and maintaining compilers and tooling, along with establishing and maintining a library ecosystem, require substantial efforts, particularly with the addition of new language features over time.

Second, users will need to adopt a new programming language and incorporate it into their existing tech stacks.
This can present a considerable challenge, as it involves a learning curve, increased cognitive load, and the necessity to introduce and manage additional tools.

## Embedded DSLs

An embedded DSL (commonly referred to as an eDSL) generally takes the form of a library in a host programming language.
Functional languages such as Haskell are particularly well-suited for hosting eDSLs, as the implementation of an eDSL largely involves functions that construct and transform abstract syntax trees (ASTs).

Embedded DSLs can be much easier than standlone DSLs to develop, and to integrate into projects that already use the host language.
Embedded DSLs, however, come with the drawback that the complexity of constructing and manipulating ASTs are exposed to the users.
When using an embedded DSL, you are essentially writing programs that create and manage ASTs, rather than straightforward code.

Take, for instance, a program that accepts two integers as input, and checks if the first is less than the second.
Normally, you would write a function of type `Integer -> Integer -> Bool`, which takes two integers and returns a boolean.
However, when working with an eDSL, your program might have a type like `AST Integer -> AST Integer -> AST Bool`, which takes two ASTs that evaluate to integers, combines them, and yields a larger AST that evaluates to a boolean.
The complexity increases further if the comparison is polymorphic, since it is unlikely that the usual method of writing polymorphic functions (such as Haskell's `Ord` instance) can be reused.
Like standalone DSLs, this also introduces additional learning curves and cognitive load, though for a different reason.

Another disadvantage of eDSLs is that it is harder, compared to the other two approaches, to produce readable target code or accurate source mappings for debuggers.
This stems from the nature of eDSLs, which are libraries that construct and manipulate ASTs.
Since they do not have direct access to the host language's ASTs, it can be challenging to retrieve information related to the source code, such as variable names, module names and code locations.

The eDSLs described above fall under the category of "deep embedding".
There's another category of eDSLs, called "shallow embedding", which, unlikely deep embedding, does not construct intermediate ASTs.
Instead, shallow embedding involves using overloaded functions.
For example, a DSL designed as a shallow embedding for working with databases might include operations such as `createTable`, `getItem`, and `putItem`.
These functions are overloaded, allowing them to work with various database implementations, including mock databases for testing purposes.
Such overloaded functions are typically defined using typeclasses in functional languages, or interfaces/traits in object-oriented languages.

While it is valid to call shallow embeddings _languages_, it is a bit of a stretch.
Overloaded functions are widespread in everyday programming, and are not usually regarded as languages due to the absence of ASTs.
Moreover, shallow embedding is less fitting when the eDSL targets a lower level language like UPLC, as constructing ASTs for UPLC will still be necessary.
All existing eDSLs targeting UPLC are examples of deep embeddings.

## Subsets of Existing Languages

Similar to eDSLs, this approach can be particularly appealing if your team or project is already using the host language.
It allows for even greater reuse of existing functions, types and idioms from the hosting language, compared to eDSLs.
For instance, a program that tests whether one integer is less than another can retain the type `forall a. Ord a => a -> a -> Bool`, and can even reuse the `<` operator in the hosting language's standard library[^1].

This is achieved by leveraging the host language's compiler frontend, which might include lexer, parser, type checker, AST and optimization passes, while developing a custom backend for the new language.
By reusing the host language's ASTs, programs maintain simple and regular types without the need for custom AST construction, which is often necessary in eDSLs.

A case in point is Plutus Tx, which is a subset of Haskell, and its compiler is a GHC plugin.
It reuses GHC components like the parser and type checker, and transforms GHC Core (GHC's intermediate representation) into UPLC.
Alternatively, meta-programming methods can be used to access and manipluate the host language's AST, such as quotes and splices[^2].

Nonetheless, developing a new language as a subset of an existing language presents several challenges.
The compiler components of the host language are most likely not tailored for the new language, and making them work for the new language can be difficult.
For example, optimizations that work well for the host language might not be effective or valid for the new language.
Additionally, the desugaring process might transform code in such a way that it no longer fits within the supported subset, causing issues with the new language’s compiler.

Furthermore, complications arise when the new language and the host language do not exactly agree on semantics or evaluation strategies.
This disparity can lead to behaviors where the same code might act differently when compiled and executed in the host language versus the new language.
It can also result in idioms that work well in the host language being inappropriate for the new language.
For example, while guarded recursion is a useful idiom in Haskell, it might not be suitable for Plutus Tx due to Plutus Tx's use of call-by-value evaluation.

Another drawback of using a subset of a language is that, determining whether a program conforms to the allowed subset typically doesn't happen at type checking time, but at target code generation time.
This not only delays error detection cmpared to eDSLs, but makes it harder to produce clear error messages, since by target code generation time, the AST may have already been transformed and optimized, obscuring its connection to the original source code.

## List of Existing Languages

| Language | Category |
| ------ | ---------- |
| Plutus Tx | Subset of Haskell |
| [Aiken](https://aiken-lang.org/) | Standalone DSL |
| [Helios](https://github.com/HeliosLang/compiler) | Standalone DSL |
| [OpShin](https://github.com/OpShin/opshin) | Subset of Python |
| [plu-ts](https://github.com/HarmonicLabs/plu-ts) | DSL embedded in TypeScript |
| [Plutarch](https://github.com/Plutonomicon/plutarch-plutus) | DSL embedded in Haskell |
| [Scalus](https://github.com/nau/scalus) | Subset of Scala |

---

[^1]: This statement is not entirely true for Plutus Tx, a subset of Haskell.
Due to certain GHC-specific technical limitations, it can't easily reuse many functions and operations from the `base` library, so it ships with its own standard library instead.
Nevertheless, the `<` operator in Plutus Tx's standard library still has the type `Integer -> Integer -> Bool`.

[^2]: For further reading, check out [_Everything old is new again: Quoted Domain Specific Languages_](https://homepages.inf.ed.ac.uk/wadler/topics/qdsl.html).
