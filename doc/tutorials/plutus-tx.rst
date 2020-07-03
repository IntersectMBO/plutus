.. highlight:: haskell
.. _what_is_plutus_tx:

What is Plutus Tx?
==================

Plutus applications are written as a single Haskell program, which
describes both the code that runs off the chain (on a user’s computer,
or in their wallet), and on the chain (as part of transaction
validation).

The parts of the program that describe the on-chain code are still just
Haskell, but they are compiled into :term:`Plutus Core` (instead of into the
normal compilation target language) and we refer to them as :term:`Plutus Tx`
("Tx" since they usually go into transactions).

.. warning::

   Strictly speaking, only a subset of Haskell is supported inside
   Plutus Tx blocks, but the majority of simple Haskell will work, and
   the Plutus Tx compiler will tell you if you use something that is
   unsupported.

The key technique that we use to implement Plutus Tx is called *staged
metaprogramming*. What that means is that the main Haskell program
generates *another* program, in this case the Plutus Core program that
will run on the blockchain. Plutus Tx is the mechanism that we use to
write those programs. But because Plutus Tx is just part of the main
Haskell program we can share types and definitions between the two.

.. _template_haskell_preliminaries:

Template Haskell preliminaries
------------------------------

Plutus Tx makes use of Template Haskell, Haskell’s metaprogramming
support. There are a few reasons for this:

1. Template Haskell allows us to do work at compile time, which is when
   we do Plutus Tx compilation.

2. It allows us to wire up the machinery that actually invokes the
   Plutus Tx compiler.

There are a lot of things you can do with Template Haskell, but we only
make very light usage of it, so we will just cover the basics here.

Template Haskell begins with *quotes*. A Template Haskell quote is a
Haskell expression ``e`` inside special brackets ``[|| e ||]``. It has
type ``Q (TExp a)`` where ``e`` has type ``a``. ``TExp a`` is a
*representation* an expression of type ``a``, i.e. the syntax of the
actual Haskell expression which was quoted. The quote lives in the type
``Q`` of quotes, which isn’t very interesting for us.

.. note::

   There is also an abbreviation ``TExpQ a`` for ``Q (TExp a)``, which
   avoids some parentheses.

You can *splice* a quote into your program using the ``$$`` operator.
This inserts the syntax represented by the quote into the program at the
point where the splice is written.

The effect of this is that quote allow us to talk about Haskell programs
as values.

The Plutus Tx compiler compiles Haskell *expressions* (not values!), so
naturally it takes a quote (representing an expression) as an argument.
The result is a new quote, this time for a Haskell program that
represents the *compiled* program. In Haskell, the type of :hsobj:`Language.PlutusTx.TH.compile`
is ``TExpQ a → TExpQ (CompiledCode PLC.DefaultUni a)``. This is just
what we already said:

-  ``TExpQ a`` is a quoted representing a program of type ``a``.

-  ``TExprQ (CompiledCode PLC.DefaultUni a)`` is quote representing a
   compiled Plutus Core program.

.. note::

   :hsobj:`Language.PlutusTx.CompiledCode` has a type parameter ``a`` as well, which
   corresponds to the type of the original expression. This lets us
   "remember" what the original type of the Haskell program that we
   compiled was.

Since :hsobj:`Language.PlutusTx.TH.compile` produces a quote, to use the result we need to splice
it back into our program. When you compile the main program, the Plutus
Tx compiler will run and the compiled program will be inserted into the
main program.

This is all the Template Haskell you need to know! We almost always use
the same, very simple pattern, which is to make a quote, immediately
call :hsobj:`Language.PlutusTx.TH.compile` and then splice the result back in, so once you are
used to that you can mostly ignore it.

.. _writing_basic_plutustx_programs:

Writing basic PlutusTx programs
-------------------------------

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK1
   :end-before: BLOCK2

Here’s the most basic program we can write: one that just evaluates to
the integer ``1``.

.. note::

   We’ve included doctests to the examples that show the Plutus Core
   that is generated from compilation. The syntax of Plutus Core will
   look unfamiliar. This is fine, since it is the "assembly language"
   and you won’t need to inspect the output of the compiler. However,
   for our purposes it’s instructive to look at it to get a vague idea
   of what’s going on.

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK2
   :end-before: BLOCK3

We can see how the metaprogramming works here: the Haskell program ``1``
was turned into a ``CompiledCode PLC.DefaultUni Integer`` at compile
time, which we spliced into our Haskell program, and which we can then
inspect at runtime to see the generated Plutus Core (or to put it on the
blockchain).

We also see the standard usage pattern here: a TH quote, wrapped in a
call to :hsobj:`Language.PlutusTx.TH.compile`, wrapped in a ``$$`` splice. This is how we write
all of our Plutus Tx programs.

Here’s a slightly more complex program, namely the identity function on
integers.

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK3
   :end-before: BLOCK4

.. _functions_and_datatypes:

Functions and datatypes
-----------------------

You can use functions inside your expression. In practice, you will
usually want to define the entirety of your Plutus Tx program as a
definition outside the quote, and then simply call it inside the quote.

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK4
   :end-before: BLOCK5

We can use normal Haskell datatypes and pattern matching freely:

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK5
   :end-before: BLOCK6

Unlike functions, datatypes do not need any kind of special annotation
to be used inside a quote, hence we can use types like ``Maybe`` from
the Haskell ``Prelude``. This works for your own datatypes too!

Here’s a small example with a datatype of our own representing a
potentially open-ended end date.

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK6
   :end-before: BLOCK7

We could also have defined the ``pastEnd`` function as a separate
``INLINABLE`` binding and just referred to it in the quote, but in this
case it’s small enough to just write in place.

.. _typeclasses:

Typeclasses
-----------

So far we have used functions like ``lessThanEqInteger`` for comparing
``Integer`` s, which is much less convenient than ``<`` from the
standard Haskell ``Ord`` typeclass.

Plutus Tx does support typeclasses, but we need to redefine the standard
typeclasses do so, since we require the class methods to be
``INLINABLE``, and the implementations for types such as ``Integer`` use
the Plutus Tx builtins.

Redefined versions of many standard typeclasses are available in the
Plutus Tx Prelude. As such you should be able to use most typeclass
functions in your Plutus Tx programs successfully.

For example, here is a version of the ``pastEnd`` function using ``<``.
This will be compiled to exactly the same code as the previous
definition.

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK7
   :end-before: BLOCK8

.. _the_plutus_tx_prelude:

The Plutus Tx Prelude
---------------------

The :hsmod:`Language.PlutusTx.Prelude` module is a drop-in replacement for
the normal Haskell Prelude, but with some functions and typeclasses
redefined to be easier for the Plutus Tx compiler to handle (i.e.
``INLINABLE``).

You should use the Plutus Tx Prelude whenever you are writing code that
you expect to compile with the Plutus Tx compiler. All of the
definitions in the Plutus Tx Prelude have working Haskell definitions,
so you can use them in normal Haskell code too, although the Haskell
Prelude versions will probably perform better.

To use the Plutus Tx Prelude, use the ``NoImplicitPrelude`` language
pragma, and import :hsmod:`Language.PlutusTx.Prelude`.

Plutus Tx has some builtin types and functions available for working
with primitive data (integers and bytestrings), as well as a few special
functions. These builtins are also exported from the Plutus Tx Prelude.

The :hsobj:`Language.PlutusTx.Builtins.error` builtin deserves a special mention. :hsobj:`Language.PlutusTx.Builtins.error` causes the
transaction to abort when it is evaluated, which one way to trigger
validation failure.

.. _lifting_values:

Lifting values
--------------

So far we’ve seen how to define pieces of code *statically* (when you
*compile* your main Haskell program), but you are likely to want to
generate code *dynamically* (when you *run* your main Haskell program).
For example, you might be writing the body of a transaction to initiate
a crowdfunding smart contract, which would need to be parameterized by
data determining the size of the goal, the campaign start and end times,
etc.

We can do this in the same way that we normally parameterize code in
functional programming: we write the static code as a *function*, and we
provide the argument later to configure it.

In our case we have a complication, in that we want to make the argument
and apply the function to it at runtime. Plutus Tx provides a mechanism
to do this called *lifting*. Lifting makes it easy to use the same types
both inside your Plutus Tx program and in the external code that uses
it.

.. note::

   When we talk about "runtime" here, we mean the runtime of the main
   Haskell program, **not** when the Plutus Core runs on the chain. We
   want to configure our code when the main Haskell program runs, as
   that is when we will be getting user input.

As a very simple example, let’s write an add-one function.

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK8
   :end-before: BLOCK9

Now, suppose we want to apply this to ``4`` at runtime, giving us a
program that computes to ``5``. We need to *lift* the argument (``4``)
from Haskell to Plutus Core, and then we need to apply the function to
it.

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK9
   :end-before: BLOCK10

We lifted the argument using the :hsobj:`Language.PlutusTx.liftCode` function. In order to use
this, a type must have an instance of the :hsobj:`Language.PlutusTx.Lift` class. In practice,
you should generate these with the :hsobj:`Language.PlutusTx.makeLift` TH function from.

.. note::

   :hsobj:`Language.PlutusTx.liftCode` is a little "unsafe" because it ignores any errors that
   might occur from lifting something that isn’t supported. There is a
   :hsobj:`Language.PlutusTx.safeLiftCode` if you want to explicitly handle these.

The combined program applies the original compiled lambda to the lifted
value (notice that the lambda is a bit complicated now since we have
compiled the addition into a builtin).

Here’s an example with our custom datatype. The output is the encoded
version of ``False``.

.. literalinclude:: PlutusTx.hs
   :start-after: BLOCK10
   :end-before: BLOCK11
