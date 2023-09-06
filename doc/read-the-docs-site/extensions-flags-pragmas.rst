.. _extensions_flags_pragmas:

GHC Extensions, Flags and Pragmas
=================================

Plutus Tx is a subset of Haskell and is compiled to Untyped Plutus Core by the Plutus Tx compiler, a GHC (Glasgow Haskell Compiler) plugin.

In order to ensure the success and correct compilation of Plutus Tx programs, all Plutus Tx modules (that is, Haskell modules that contain code to be compiled by the Plutus Tx compiler) should use the following GHC extensions, flags and pragmas.


Extensions
-------------------------------------------------

Plutus Tx modules should use the ``Strict`` extension: ::

  {-# LANGUAGE Strict #-}

Unlike in Haskell, function applications in Plutus Tx are strict.
In other words, when evaluating ``(\x -> 42) (3 + 4)`` the expression ``3 + 4`` is evaluated first, before evaluating the function body (``42``), even though ``x`` is not used in the function body.
The ``Strict`` extension ensures that let bindings and patterns are also (by default) strict, for instance, evaluating
``let x = 3 + 4 in 42`` evaluates ``3 + 4`` first, even though ``x`` is not used.

Bang patterns and lazy patterns can be used to explicitly specify whether a let binding is strict or non-strict, as in ``let !x = 3 + 4 in 42`` (strict) and ``let ~x = 3 + 4 in 42`` (non-strict).
At this time, it is not possible to make function applications non-strict: ``(\(~x) -> 42) (3 + 4)`` still evaluates ``3 + 4`` strictly.

Making let bindings strict by default has the following advantages:

* It makes let bindings and function applications semantically equivalent, e.g., ``let x = 3 + 4 in 42`` has the same semantics as ``(\x -> 42) (3 + 4)``.
  This is what one would come to expect, as it is the case in most other programming languages, regardless of whether the language is strict or non-strict.
* Untyped Plutus Core programs, which are compiled from Plutus Tx, are not evaluated lazily (unlike Haskell), that is, there is no memoization of the results of evaluated expressions.
  Thus using non-strict bindings can cause an expression to be inadvertently evaluated for an unbounded number of times.
  Consider ``let x = <expensive> in \y -> x + y``.
  If ``x`` is non-strict, ``<expensive>`` will be evalutated every time ``\y -> x + y`` is applied to an argument, which means it can be evaluated 0 time, 1 time, 2 times, or any number of times (this is not the case if lazy evaluation was employed).
  On the other hand, if ``x`` is strict, it is always evaluated once, which is at most one more time than what is necessary.

Flags
-------------------------------------------------

GHC has a variety of optimization flags, many of which are on by default.
Although Plutus Tx is, syntactically, a subset of Haskell, it has different semantics and a different evaluation strategy (Haskell: non-strict semantics, call by need; Plutus Tx: strict semantics, call by value).
As a result, some GHC optimizations are not helpful for Plutus Tx programs, and can even be harmful, in the sense that it can make Plutus Tx programs less efficient, or fail to be compiled.
An example is the full laziness optimization, controlled by GHC flag ``-ffull-laziness``, which floats let bindings out of lambdas whenever possible.
Since Untyped Plutus Core does not employ lazy evaluation, the full laziness optimization is usually not beneficial, and can sometimes make a Plutus Tx program more expensive.
Conversely, some GHC features must be turned on in order to ensure Plutus Tx programs are compiled successfully.

All Plutus Tx modules should use the following GHC flags: ::

  -fno-ignore-interface-pragmas
  -fno-omit-interface-pragmas
  -fno-full-laziness
  -fno-spec-constr
  -fno-specialise
  -fno-strictness
  -fno-unbox-strict-fields
  -fno-unbox-small-strict-fields

``-fno-ignore-interface-pragmas`` and ``-fno-omit-interface-pragmas`` ensure unfoldings of Plutus Tx functions are available.
The rest are GHC optimizations that are generally bad for Plutus Tx, and should thus be turned off.

These flags can be specified either in a Haskell module, e.g.: ::

  {-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}

or in a build file. E.g., if your project is built using Cabal, you can add the flags to the ``.cabal`` files, like so:

  ghc-options:
    -fno-ignore-interface-pragmas

Note that this section only covers GHC flags, not Plutus Tx compiler flags.
Information about the latter can be found in :ref:`plutus_tx_options`.

Pragmas
-------------------------------------------------

All functions and methods should have the ``INLINEABLE`` pragma, so that their unfoldings are made available to the Plutus Tx compiler.

The ``-fexpose-all-unfoldings`` flag also makes GHC expose all unfoldings, but unfoldings exposed this way can be more optimized than unfoldings exposed via ``INLINEABLE``.
In general we do not want GHC to perform optimizations, since GHC optimizes a program based on the assumption that it has non-strict semantics and is evaluated lazily (call by need), which is not true for Plutus Tx programs.
Therefore, ``INLINEABLE`` is preferred over ``-fexpose-all-unfoldings`` even though the latter is simpler.

``-fexpose-all-unfoldings`` can be useful for functions that are generated by GHC and do not have the ``INLINEABLE`` pragma.
``-fspecialise`` and ``-fspec-constr`` are two examples of optimizations that can generate such functions.
The most reliable solution, however, is to simply turn these optimizations off.
Another option is to bump ``-funfolding-creation-threshold`` to make it more likely for GHC to retain unfoldings for functions without the ``INLINEABLE`` pragma.
``-fexpose-all-unfoldings`` should be used as a last resort.
