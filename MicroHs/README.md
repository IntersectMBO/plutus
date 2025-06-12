# Micro Haskell
This repository contains an implementation of an extended subset of Haskell.
It uses combinators for the runtime execution.

The runtime system has minimal dependencies, and can be compiled even for micro-controllers.
The `boards/` directory contains some samples, e.g., some sample code for an STM32F407G-DISC1 board.

The compiler can compile itself.

## Presentation
You can find my [presentation from the Haskell Symposium 2024](https://docs.google.com/presentation/d/1WsSiSwypNVTm0oZ3spRYF8gA59wyteOsIkPRjCUAZec/edit?usp=sharing), [video](https://m.youtube.com/watch?v=uMurx1a6Zck&t=36m).
There is also a short paper in `doc/hs2024.pdf`.

## Compiling MicroHs
There are two different ways to compile MicroHs:
* Using GHC. `Makefile` target `bin/gmhs`
* Using the included combinator file and runtime.  `Makefile` target `bin/mhs`

These different ways of compiling need slightly different imports etc.
This happens by GHC looking in the `ghc/` subdirectory first for any extras/overrides.

Compiling MicroHs is really best done using `make`, but there is also a `MicroHs.cabal` file
for use with `cabal`/`mcabal`.  This only builds what corresponds to the first target.
Doing `cabal install` will install the compiler.
Note that `mhs` built with ghc does not have all the functionality.

Also note that there is no need to have a Haskell compiler to run MicroHs.
All you need is a C compiler, and MicroHs can bootstrap, given the included combinator file.

To install `mhs` use `make minstall`.  This will install `mhs` in `~/.mcabal` in the same
way as `mcabal` (MicroCabal) would have.  It will install a compiler binary and a compiled base package.
You will have to add `~/.mcabal/bin` to your `PATH`.

Alternatively, to install `mhs` use `make oldinstall`.  By default this copies the files to `/usr/local`,
but this can be overridden by `make PREFIX=dir oldinstall`.
You also need to set the environment variable `MHSDIR`.

To compile on Windows make sure `cl` is in the path, and then use `nmake` with `Makefile.windows`.

The compiler can also be used with emscripten to produce JavaScript/WASM.

## Language
The language is an extended subset of Haskell-2010.

Differences:
 * There is only deriving for `Bounded`, `Enum`, `Eq`, `Ord`, `Show`, and `Typeable`.
 * Kind variables need an explicit `forall`.
 * Always enabled extension:
   * AllowAmbiguousTypes
   * BangPatterns
   * BinaryLiterals
   * BlockArguments
   * ConstraintKinds
   * DefaultSignatures
   * DeriveAnyClass
   * DerivingStrategies
   * DerivingVia
   * DoAndIfThenElse
   * DuplicateRecordFields
   * EmptyCase
   * EmptyDataDecls
   * ExistentialQuantification
   * ExplicitNamespaces
   * ExtendedDefaultRules
   * FlexibleContexts
   * FlexibleInstance
   * ForeignFunctionInterface
   * FunctionalDependencies
   * GADTs
   * GADTsyntax
   * GeneralizedNewtypeDeriving
   * ImportShadowing
   * ImportQualifiedPost
   * IncoherentInstances
   * InstanceSigs
   * KindSignatures
   * LambdaCase
   * LiberalTypesynonyms
   * MonoLocalBinds
   * MultilineStrings
   * MultiParamTypeClasses
   * MultiWayIf
   * NamedDefaults
   * NamedFieldPuns
   * NegativeLiterals
   * NoMonomorphismRestriction
   * NoStarIsType
   * NumericUnderscores
   * OrPatterns
   * OverlappingInstances
   * OverloadedRecordDot
   * OverloadedRecordUpdate
   * OverloadedStrings
   * PatternSynonyms
   * PolyKinds
   * PolymorphicComponents
   * RankNTypes
   * RecordWildCards
   * RequiredTypeArguments
   * QualifiedDo
   * ScopedTypeVariables
   * StandaloneDeriving
   * StandaloneKindSignatures
   * TupleSections (only pairs right now)
   * TypeApplications
   * TypeLits
   * TypeSynonymInstances
   * UndecidableInstances
   * UndecidableSuperClasses
   * UnicodeSyntax
   * ViewPatterns
 * The only extension that is not always on is `CPP`.
 * `main` in the top module given to `mhs` serves at the program entry point.
 * Many things that should be an error (but which are mostly harmless) are not reported.
 * Text file I/O always uses UTF8, as does the source code.
 * The `BangPatterns` extension is parsed, but only effective at the a top level `let`/`where`.
 * More differences that I don't remember right now.

Mutually recursive modules are allowed the same way as with GHC, using `.hs-boot` files.

## Example
The file `Example.hs` contains the following:
```Haskell
module Example(main) where

fac :: Int -> Int
fac 0 = 1
fac n = n * fac(n-1)

main :: IO ()
main = do
  let rs = map fac [1,2,3,10]
  putStrLn "Some factorials"
  print rs
```

First, make sure the compiler is built by doing `make`.
Then compile the file by `bin/mhs Example -oEx` which produces `Ex`.
Finally, run the binary file by `./Ex`.
This should produce
```
Some factorials
[1,2,6,3628800]
```

## Libraries
The `Prelude` contains the functions from the Haskell Report and a few extensions,
with the notable exception that `Foldable` and `Traversable` are not part of the `Prelude`.
They can be imported separately, though.

### Not importing `Prelude`
To completely avoid importing the prelude (which can be needed in base to
avoid circular imports) use the incantation `import qualified Prelude()`.
This will not even try to open `Prelude.hs`.  It also avoids the automagic
(qualified) import of `Mhs.Builtin` that normally happens.

## Types
There are some primitive data types, e.g `Int`, `IO`, `Ptr`, and `Double`.
These are known by the runtime system and various primitive operations work on them.
The function type, `->`, is (of course) also built in.

All other types are defined with the language.  They are converted to lambda terms using
an encoding.
For types with few constructors (< 5) it uses Scott encoding, otherwise it is a pair with
an integer tag and a tuple (Scott encoded) with all arguments.
The runtime system knows how lists and booleans are encoded.

## Compiler
The compiler is written in Micro Haskell.
It takes a name of a module (or a file name) and compiles to a target (see below).
This module should contain the function `main` of type `IO ()` and
it will be the entry point to the program.

### Compiler flags
* `--version` show version number
* `-i` set module search path to empty
* `-iDIR` append `DIR` to module search path
* `-oFILE` output file.  If the `FILE` ends in `.comb` it will produce a textual combinator file.  If `FILE` ends in `.c` it will produce a C file with the combinators.  For all other `FILE` it will compile the combinators together with the runtime system to produce a regular executable.
* `-r` run directly
* `-v` be more verbose, flag can be repeated
* `-CW` write compilation cache to `.mhscache` at the end of compilation
* `-CR` read compilation cache from `.mhscache` at the start of compilation
* `-C` short for `-CW` and `-CR`
* `-T` generate dynamic function usage statistics
* `-z` compress combinator code generated in the `.c` file
* `-l` show every time a module is loaded
* `-s` show compilation speed in lines/s
* `-XCPP` run `cpphs` on source files
* `-Dxxx` passed to `cpphs`
* `-Ixxx` passed to `cpphs`
* `-tTARGET` select target
* `-a` set package search path to empty
* `-aDIR` prepend `DIR` to package search path
* `-PPKG` create package `PKG`
* `-L[FILE]` list all modules in a package
* `-Q FILE [DIR]` install package
* `-ddump-PASS` debug, show AST after `PASS`.  Possible passes `parse`, `derive`, `typecheck`, `desugar`, `toplevel`, `combinator`, `all`
* `--` marks end of compiler arguments

With the `-v` flag the processing time for each module is reported.
E.g.
  ```
  importing done MicroHs.Exp, 284ms (91 + 193)
  ```
which means that processing the module `MicroHs.Exp` took 284ms,
with parsing taking 91ms and typecheck&desugar taking 193ms.

With the `-C` flag the compiler writes out its internal cache of compiled modules to the file `.mhscache`
at the end of compilation.  At startup it reads this file if it exists, and then validates the contents
by an MD5 checksum for all the files in the cache.
This can make compilation much faster since the compiler will not parse and typecheck a module if it is in
the cache.
Do **NOT** use `-C` when you are changing the compiler itself; if the cached data types change the compiler will probably just crash.

### Targets
The configuration file `targets.conf` (in the installation directory) defines how to compile for
different targets.  As distributed it contains the targets `default` and `emscripten`.
The first is the normal target to run on the host.
The `emscripten` target uses `emcc` to generate JavaScript/WASM.
If you have `emcc` and `node` installed you can do
  ```
  mhs -temscripten Example -oout.js; node out.js
  ```
to compile and run the JavaScript.  The generated JavaScript file has some regular JavaScript,
and also the WASM code embedded as a blob.  Running via JavaScript/WASM is almost as fast as running natively.

### Environment variables
* `MHSDIR` the directory where `lib/` and `src/` are expected to be.  Defaults to `./`.
* `MHSCC` command use to compile C file to produce binaries.  Look at the source for more information.
* `MHSCPPHS` command to use with `-XCPP` flag.  Defaults to `cpphs`.
* `MHSCONF` which runtime to use, defaults to `unix-32/64` depending on your host's word size
* `MHSEXTRACCFLAGS` extra flags passed to the C compiler

### Compiler modules

* `Abstract`, combinator bracket abstraction and optimization.
* `Compile`, top level compiler.  Maintains a cache of already compiled modules.
* `CompileCache`, cache for compiled modules.
* `Deriving`, do deriving for various type classes.
* `Desugar`, desugar full expressions to simple expressions.
* `EncodeData`, data type encoding.
* `Exp`, simple expression type.
* `ExpPrint`, serialize `Exp` for the runtime system.
* `Expr`, parsed expression type.
* `FFI`, generate C wrappers for FFI.
* `Fixity`, resolve operator fixities.
* `Flags`, compiler flags.
* `Graph`, strongly connected component algorithm.
* `Ident`, identifiers and related types.
* `IdentMap`, map from identifiers to something.
* `Interactive`, top level for the interactive REPL.
* `Lex`, lexical analysis and indentation processing.
* `Main`, the main module.  Decodes flags, compiles, and writes result.
* `MakeCArray`, generate a C version of the combinator file.
* `Parse`, parse and build and abstract syntax tree.
* `StateIO`, state + IO monad.
* `SymTab`, symbol table manipulation.
* `TCMonad`, type checking monad.
* `Translate`, convert an expression tree to its value.
* `TypeCheck`, type checker.

## Interactive mode
If no module name is given the compiler enters interactive mode.
You can enter expressions to be evaluated, or top level definitions (including `import`).
Simple line editing is available.

All definitions are saved in the file `Interactive.hs` and all input
lines as saved in `.mhsi`.  The latter file is read on startup so
the command history is persisted.

Available commands:

* `:quit` Quit the interactive system
* `:clear` Get back to start state
* `:del STR` Delete all definitions that begin with `STR`
* `:reload` Reload all modules
* `:type EXPR` Show type of `EXPR`
* `:kind TYPE` Show kind of `TYPE`
* `:set FLAG` Set flag
* `expr` Evaluate expression.
* `defn` Add definition (can also be an `import`)

## MHS as a cross compiler
When `mhs` is built, targets.conf is generated. It will look something like this:
```ini
[default]
cc = "cc"
conf = "unix-64"
```

You can add other targets to this file, changing which compiler command is used and which runtime is
selected and then use the `-t` argument to select which target you would like.

## Packages
To avoid compiling everything from source all the time there is a notion of a precompiled package.
A package is simply a set of modules that are compiled together and that can then be installed in
a known place (typically `~/.mcabal/mhs-VERSION/packages/`).
Packages can depend on already installed packages.

There is a search path for installed packages, controlled by the `-a` flag.

There is no need for any extra flags to `mhs` to use installed packages, they are all visible at all times.
When compiling to a binary only the used parts of a package will be included in the binary.

### Compiling a package
To compile a package use the command `mhs -Ppackage-name.pkg modules...` where `modules...`
are all the modules you wish to expose from the package.  If other modules are needed they will
automatically be included in the package.
You typically also want to use the `-o` flag to give the package a sensible name.

### Installing a package
To install a package use the command `mhs -Q package-name.pkg [install-dir]`.
If the `install-dir` is left out the package is installed in the default place.

### MicroCabal (`mcabal`)
Normally a package is downloaded from hackage and it will have a `.cabal` file
that describes the package contents.  To install a downloaded package simply
do `mcabal install`.  The `mcabal` program is included in the MicroHs download.
You can also do `mcabal install PKG` to download an install a package.

### Installed package organization
The packages are typically installed in `~/.mcabal/` and it has the following
layout:
* `.mcabal/bin/` installed binaries, initially `mhs`, `cpphs`, and `mcabal`
* `.mcabal/mhs-VER/` installed files for the given `mhs` version
* `.mcabal/mhs-VER/packages/` for each library package a `PKG.pkg` file (the binary blob for the package)
  and also (maybe) a directory `PKG/` that contains `data/`, `include/`, and `cbits/` for the package.
* `.mcabal/.../MODULE.txt` a file for each installed module, it contains the name of the package the contains that module.

For example, after installing `mhs` version 0.10.5.0 we will have something like this:
```
.mcabal/
        bin/cpphs
            mcabal
            mhs
        mhs-0.10.5.0/Control/Applicative.txt   -- contains "base-0.10.5.0.pkg"
                             ...
                             Monad/Fail.txt    -- contains "base-0.10.5.0.pkg"
                                   ...
                             ...
                     Data/
                     ...
                     Prelude.txt               -- contains "base-0.10.5.0.pkg"
        packages/base-0.10.5.0.pkg
                 mhs-0.10.5.0/data/src/runtime/eval.c
                                               ...
```


A (maybe) short-coming of the package system is that there can only be one version of a
package installed at a time.  If you need multiple version, you have to use different directories for them
and use `-a` to control it.  There is absolutely no checks for consistency among packages.
There is also no compatibility between packages compiled with different versions of the compiler.

### Hackage
Hackage is full of great packages, unfortunately most of them contain some GHC specific code.
There is a handful packages that works with mhs out of the box, or have been converted:
* `containers`
* `cpphs`
* `hscolour`
* `mtl` changes not merged yet, use [github.com/augustss/mtl](https://github.com/augustss/mtl)
* `parsec` changes not merged yet, use [github.com/augustss/parsec](https://github.com/augustss/parsec)
* `polyparse`
* `pretty`
* `time`
* `transformers`

Some of these might not have be released on hackage yet, but the github repo works.

Contributions to this list are very welcome.

## Files
There is a number of subdirectories:
* `Tools/` a few useful tools for compressions etc.
* `bin/` executables are put here
* `generated/` this contains the (machine generated) combinator file for the compiler.
* `lib/` this contains the `Prelude` and other base library file.
* `src/MicroHs/` the compiler source
* `src/runtime/` the runtime source
* `tests/` some tests

## Runtime
The runtime system is written in C and is in `src/runtime/eval.c`.
It uses combinators for handling variables, and has primitive operations
for built in types and for executing IO operations.
There is a also a simple mark-scan garbage collector.
The runtime system is written in a reasonably portable C code.

### Runtime flags
Runtime flags are given between the flags `+RTS` and `-RTS`.
Between those the runtime decodes the flags, everything else is available to
the running program.

* `-HSIZE` set heap size to `SIZE` cells, can be suffixed by `k`, `M`, or `G`, default is `50M`
* `-KSIZE` set stack size to `SIZE` entries, can be suffixed by `k`, `M`, or `G`, default is`100k`
* `-rFILE` read combinators from `FILE`, instead of `out.comb`
* `-v` be more verbose, flag can be repeated
* `-T` generate profiling stats (if compiled with `-T` as well)
* `-B` ring the bell on every GC
* `-oFILE` just read the input, run garbage collection, and write out the resulting graph to file.

For example, `bin/mhseval +RTS -H1M -v -RTS hello` runs `out.comb` and the program gets the argument `hello`,
whereas the runtime system sets the heap to 1M cells and is verbose.

### FFI
MicroHs supports calling C functions.
When running the program directly (using `-r`) or when generating a `.comb` file only the functions in the table built
into `src/runtime/eval.c` can be used.  When generating a `.c` file or an executable any C function can be called.

There is a lot of missing FFI functionality compared to GHC.

### Records
MicroHs implements the record dot extensions.
So accessing a field `a` in record `r` is written `r.a`, as well as the usual `a r`.
The former is overloaded and can access any `a` field, whereas the latter is the usual monomorphic field selector.
Updating a field has the usual Haskell syntax `r{ a = e }`, but the type is overloaded so this can update the `a` field in any record.
The typeclasses `HasField` and `SetField` capture this.
`HasField "name" rec ty` expresses that the record type `rec` has a field `name` with type `ty` that can be extracted with `getField`.
`SetField "name" rec ty` expresses that the record type `rec` has a field `name` with type `ty` that can be set `setField`.

Record updates can also update nested fields, e.g., `r{ a.b.c = e }`.  Note that this will not easily work in GHC, since GHC does not
fully implement `OverloadedRecordUpdate`.  When GHC decides how to do it, MicroHs will follow suit.

Note that record updates cannot change the type of polymorphic fields.

### Serialization
The runtime system can serialize and deserialize any expression
and keep its graph structure (sharing and cycles).
The only exceptions to this are C pointers (e.g., file handles),
which cannot be serialized (except for `stdin`, `stdout`, and `stderr`).

### Memory layout
Memory allocation is based on cells.  Each cell has room for two pointers (i.e., two words, typically 16 bytes),
so it can represent an application node.  One bit is used to indicate if
the cell is an application or something else.  If it is something else one
word is a tag indicating what it is, e.g., a combinator or an integer.
The second word is then used to store any payload, e.g., the number itself for an integer node.

Memory allocation has a bitmap with one bit per cell.
Allocating a cell consists of finding the next free cell using the bitmap,
and then marking it as used.  The garbage collector first clears the bitmap
and then (recursively) marks every used cell in the bitmap.
There is no explicit scan phase since that is baked into the allocation.
Allocation is fast assuming the CPU has some kind of FindFirstSet instruction.

It is possible to use smaller cells by using 32 bit "pointers" instead of 64 bit pointers.
This has a performance penalty, though.

### Portability
The C code for the evaluator does not use any special features, and should be
portable to many platforms.  It has mostly been tested with MacOS and Linux,
and somewhat with Windows.

The code has been tested on 64- and 32-bit little-endian platforms.

The `src/runtime/` directory contains configuration files for different platform.
Use the appropriate `src/runtime/eval-`*platform*`.c`.

## Bootstrapping
The compiler can compile itself.  To replace `bin/mhs` with a new version,
do `make bootstrap`.  This will recompile the compiler twice and compare
the outputs to make sure the new compiler still works.

### Bootstrapping with Hugs
It is also possible to bootstrap MicroHs using Hugs.  That means that
MicroHs can be built from scratch in the sense of [bootstrappable.org](https://bootstrappable.org/).
To compile with Hugs you need [a slightly patched version of Hugs](https://github.com/augustss/hugs98-plus-Sep2006)
and also the [hugs branch of MicroHs](https://github.com/augustss/MicroHs/tree/hugs).

The patched version of Hugs is needed to work around undefined behavior with arithmatic overflow.
Hugs provided Linux distribtions or other third party package managers may or may not work.

## Using GMP for `Integer`
The default implementation of the `Integer` type is written is Haskell and is quite slow.
It is possible to use the [GMP](https://gmplib.org/) library instead.
To use GMP you need to uncomment the first few lines in the `Makefile`, and also
modify the definition that directs the C compiler where to find GMP.

***NOTE*** To switch between using and not using GMP you need to do `make clean`.
You might also need to do `make USECPPHS=cpphs bootstrapcpphs` if there are complaints.

# Preprocessor
Sadly, compiling a lot of Haskell packages needs the C preprocessor.
To this end, the distribution contains the combinator code for `cpphs`.
Doing `make bin/cpphs` will create the binary for the preprocessor.

To bootstrap `cpphs` you can do `make bootstrapcpphs`.
This assumes that you have `git` to download the needed packages.
At the moment, the downloaded packages are forks of the original to
make it compile with `mhs`.

To identify that it is MicroHs that is the compiler it defines the symbol `__MHS__`.

# Contributing
Contributions are very welcome!

When modifying the compiler, run `make newmhs` or `make newmhsz` (the latter compresses the binary)
to generate a compiler that includes your changes.

## Libraries

The libraries live in the `lib/` directory. Adding missing functions/instances/types from the report is a welcome contribution.
Common things from `base` and GHC boot libraries that use a lot of GHC-specific code (such as `array`, `bytestring`, `text`, ...) can also be added.

## Tests

The test suite is located in the `tests/` directory.

To add a new test, create a `MyTest.hs` file and a corresponding `MyTest.ref` file for the expected output.
Then add it to the `test` rule in `tests/Makefile`:
```makefile
	$(TMHS) MyTest     && $(EVAL) > MyTest.out     && diff MyTest.ref MyTest.out
```

If you want to test that a module fails to compile with a certain error message,
add it to `tests/errmsg.test`, for example:
```
module E() where
x :: Int
x = y
-----
"../tmp/E.hs": line 4, col 5: undefined value: y

=====
```

To run the test suite, do
* `make runtest` to use the GHC-compiled compiler
* `make runtestmhs` to use the MicroHs-compiled compiler
* `make runtestemscripten` to use the MicroHs-compiled compiler targeting JavaScript

## Primitives

If you want to add a new primitive, you need to modify a few things:
* in `src/runtime/eval.c`
  - add a variant to `enum node_tag`
  - add an entry to the `primops` table (mapping the name of your primitive to the tag)
  - add a `case` in `printrec`
  - implement the primitive by adding a `case` in `evali` (you can use the other primitives as a guide)
* in `src/MicroHs/Translate.hs`
  - add an entry to the `primTable`, to make the primitive available in the interactive mode
* in `ghc/PrimTable.hs`
  - add an entry to `primOps`, if the primitive should be available in the GHC-compiled interactive mode
* in `hugs/PrimTable.hs`
  - add an entry to `primOps`, if the primitive should be available in the Hugs-compiled interactive mode

Then you can use the primitive via the `_primitive` keyword (`_primitive "myPrimitive"`).

# Thank You
A big thanks goes to the people who have contributed to MicroHs:
@dmjio
gay@disroot.org
@gergoerdi
@jmaessen
@juhp
@kolmodin
@konsumlamm
@liolin
@rewbert
@thimc
@treeowl
@TristanCacqueray
@yobson


# FAQ
*
  * Q: When will it get _insert feature_?
  * A: Maybe some time, maybe never.  But it doesn't hurt to ask for it.
*
  * Q: Why are the error messages so bad?
  * A: Error messages are boring.
*
  * Q: Why is the so much source code?
  * A: I wonder this myself.  10000+ lines of Haskell seems excessive.
       6000+ lines of C is also more than I'd like for such a simple system.
