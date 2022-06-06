.. highlight:: haskell
.. _plutus_tx_tutorial:

Using Plutus Tx
===============

Plutus applications are written as a single Haskell program, which describes both the code that runs off the chain (on a user’s computer, or in their wallet, for example), and on the chain as part of transaction validation.

The parts of the program that describe the on-chain code are still just Haskell, but they are compiled into :term:`Plutus Core`, rather than into the normal compilation target language.
We refer to them as :term:`Plutus Tx` programs (where 'Tx' indicates that these components usually go into transactions).

.. warning::

   Strictly speaking, while the majority of simple Haskell will work, only a subset of Haskell is supported by the Plutus Tx compiler.
   The Plutus Tx compiler will tell you if you are attempting to use an unsupported component.

The key technique that we use to implement Plutus Tx is called *staged metaprogramming*, which means that the main Haskell program generates *another* program (in this case, the Plutus Core program that will run on the blockchain).
Plutus Tx is the mechanism we use to write those programs, but since Plutus Tx is just part of the main Haskell program, we can share types and definitions between the two.

.. _template_haskell_preliminaries:

Template Haskell preliminaries
------------------------------

Plutus Tx uses Haskell's metaprogramming support, Template Haskell, for two main reasons:

-  Template Haskell enables us to work at compile time, which is when we do Plutus Tx compilation.
-  It allows us to wire up the machinery that invokes the Plutus Tx compiler.

Template Haskell is very versatile, but we only use a few features.

Template Haskell begins with *quotes*.
A Template Haskell quote is a Haskell expression ``e`` inside special brackets ``[|| e ||]``.
It has type ``Q (TExp a)`` where ``e`` has type ``a``. ``TExp a`` is a *representation* an expression of type ``a``, i.e. the syntax of the actual Haskell expression that was quoted.
The quote lives in the type ``Q`` of quotes, which isn’t very interesting for us.

.. note::

   There is also an abbreviation ``TExpQ a`` for ``Q (TExp a)``, which avoids some parentheses.

You can *splice* a quote into your program using the ``$$`` operator.
This inserts the syntax represented by the quote into the program at the point where the splice is written.

Simply put, a quote allows us to talk about Haskell programs as *values*.

The Plutus Tx compiler compiles Haskell *expressions* (not values!), so naturally it takes a quote (representing an expression) as an argument.
The result is a new quote, this time for a Haskell program that represents the *compiled* program.
In Haskell, the type of :hsobj:`PlutusTx.TH.compile` is ``TExpQ a → TExpQ (CompiledCode a)``.
This is just what we already said:

-  ``TExpQ a`` is a quoted representing a program of type ``a``.

-  ``TExpQ (CompiledCode a)`` is quote representing a
   compiled Plutus Core program.

.. note::

   :hsobj:`PlutusTx.CompiledCode` also has a type parameter ``a``, which corresponds to the type of the original expression.
      This lets us "remember" the type of the original Haskell program we compiled.

Since :hsobj:`PlutusTx.TH.compile` produces a quote, to use the result we need to splice it back into our program.
The Plutus Tx compiler runs when compiling the main program, and the compiled program will be inserted into the main program.

This is all you need to know about the Template Haskell!
We often use the same simple pattern: make a quote, immediately call :hsobj:`PlutusTx.TH.compile`, and then splice the result back in.

.. _writing_basic_plutustx_programs:

Writing basic Plutus Tx programs
--------------------------------

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK1
   :end-before: BLOCK2

This simple program just evaluates to the integer ``1``.

.. note::
   The examples that show the Plutus Core generated from compilation include doctests.
   The syntax of Plutus Core might look unfamiliar, since this syntax is used for the 'assembly language', which means you don't need to inspect the compiler's output.
   But for the purpose of this tutorial, it is useful to understand what is happening.

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK2
   :end-before: BLOCK3

We can see how the metaprogramming works: the Haskell program ``1`` was turned into a ``CompiledCode Integer`` at compile time, which we spliced into our Haskell program.
We can inspect the generated program at runtime to see the generated Plutus Core (or to put it on the blockchain).

We also see the standard usage pattern: a TH quote, wrapped in a call to :hsobj:`PlutusTx.TH.compile`, wrapped in a ``$$`` splice.
This is how all our Plutus Tx programs are written.

This is a slightly more complex program. It includes the identity function on integers.

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK3
   :end-before: BLOCK4

.. _functions_and_datatypes:

Functions and datatypes
-----------------------

You can use functions inside your expression.
In practice, you will usually want to define the entirety of your Plutus Tx program as a definition outside the quote, and then simply call it inside the quote.

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK4
   :end-before: BLOCK5

We can use normal Haskell datatypes and pattern matching freely:

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK5
   :end-before: BLOCK6

Unlike functions, datatypes do not need any kind of special annotation to be used inside a quote, hence we can use types like ``Maybe`` from the Haskell ``Prelude``.
This works for your own datatypes too!

Here’s a small example with a datatype representing a potentially open-ended end date.

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK6
   :end-before: BLOCK7

We could also have defined the ``pastEnd`` function as a separate ``INLINABLE`` binding and just referred to it in the quote, but in this case, it’s small enough to just write in place.

.. _typeclasses:

Typeclasses
-----------

So far we have used functions like ``lessThanEqInteger`` for comparing ``Integer`` s, which is much less convenient than ``<`` from the standard Haskell ``Ord`` typeclass.

Plutus Tx does support typeclasses, but we cannot use many of the standard typeclasses, since we require their class methods to be ``INLINABLE``, and the implementations for types such as ``Integer`` use the Plutus Tx built-ins.

Redefined versions of many standard typeclasses are available in the Plutus Tx Prelude.
As such, you should be able to use most typeclass functions in your Plutus Tx programs.

For example, here is a version of the ``pastEnd`` function using ``<``.
This will be compiled to exactly the same code as the previous definition.

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK7
   :end-before: BLOCK8

.. _the_plutus_tx_prelude:

The Plutus Tx Prelude
---------------------

The :hsmod:`PlutusTx.Prelude` module is a drop-in replacement for the normal Haskell Prelude, with some redefined functions and typeclasses that makes it easier for the Plutus Tx compiler to handle (i.e.``INLINABLE``).

Use the Plutus Tx Prelude for code that you expect to compile with the Plutus Tx compiler.
All the definitions in the Plutus Tx Prelude include working Haskell definitions, which means that you can use them in normal Haskell code too, although the Haskell Prelude versions will probably perform better.

To use the Plutus Tx Prelude, use the ``NoImplicitPrelude`` language pragma and import :hsmod:`PlutusTx.Prelude`.

Plutus Tx includes some built-in types and functions for working with primitive data (integers and bytestrings), as well as a few special functions.
These types are also exported from the Plutus Tx Prelude.

The :hsobj:`PlutusTx.Builtins.error` built-in deserves a special mention.
:hsobj:`PlutusTx.Builtins.error` causes the transaction to abort when it is evaluated, which is one way to trigger a validation failure.

.. _lifting_values:

Lifting values
--------------

So far we’ve seen how to define pieces of code *statically* (when you *compile* your main Haskell program), but you might want to generate code *dynamically* (that is, when you *run* your main Haskell program).
For example, you might be writing the body of a transaction to initiate a crowdfunding smart contract, which would need to be parameterized by data determining the size of the goal, the campaign start and end times, etc.

We can do this in the same way that we parameterize code in functional programming: write the static code as a *function* and provide the argument later to configure it.

In our case, there is a slight complication: we want to make the argument and apply the function to it at *runtime*.
Plutus Tx addresses this through *lifting*.
Lifting enables the use of the same types, both inside your Plutus Tx program *and* in the external code that uses it.

.. note::

   In this context, *runtime* means the runtime of the main Haskell program, **not** when the Plutus Core runs on the chain.
   We want to configure our code when the main Haskell program runs, as that is when we will be getting user input.

In this example, we add an add-one function.

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK8
   :end-before: BLOCK9

Now, suppose we want to apply this to ``4`` at runtime, giving us a program that computes to ``5``.
We need to *lift* the argument (``4``) from Haskell to Plutus Core, and then we need to apply the function to it.

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK9
   :end-before: BLOCK10

We lifted the argument using the :hsobj:`PlutusTx.liftCode` function.
To use this, a type must have an instance of the :hsobj:`PlutusTx.Lift` class.
For your own datatypes you should generate these with the :hsobj:`PlutusTx.makeLift` TH function from :hsmod:`PlutusTx.Lift`.

.. note::

   :hsobj:`PlutusTx.liftCode` is relatively unsafe because it ignores any errors that might occur from lifting something that might not be supported.
   There is a :hsobj:`PlutusTx.safeLiftCode` if you want to explicitly handle these occurrences.

The combined program applies the original compiled lambda to the lifted value (notice that the lambda is a bit complicated now, since we have compiled the addition into a built-in).

Here’s an example with our custom datatype.
The output is the encoded version of ``False``.

.. literalinclude:: BasicPlutusTx.hs
   :start-after: BLOCK10
   :end-before: BLOCK11

Plutus Tx Compiler Options
--------------------------

A number of options can be passed to the Plutus Tx compiler. See :ref:`plutus_tx_options`
for details.
