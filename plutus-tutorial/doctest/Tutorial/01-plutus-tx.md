# Plutus Tx Tutorial

This tutorial will walk you through the basics of using the Plutus Tx compiler to create
embedded programs that can be used when generating transactions.

This is the first in a series of tutorials:

1. Plutus Tx (this one)
2. [A guessing game](./02-validator-scripts.md)
3. [A crowdfunding campaign](./03-wallet-api.md)
4. [Working with the emulator](../../tutorial/Tutorial/Emulator.hs)
5. [A multi-stage contract](../../tutorial/Tutorial/Vesting.hs)

We assume the reader is familiar with the [introductory material](../../tutorial/Intro.md).
Some basic familiarity with Template Haskell (TH) is also helpful.

## What is Plutus Tx?

Plutus Tx is the name that we give to specially-delimited sections of a
Haskell program which will be compiled into Plutus Core (usually to go in
a transaction, hence the "Tx"). 

This means that Plutus Tx *is just Haskell*. Strictly, only a subset of Haskell
is supported, but most simple Haskell should work, and the compiler will tell
you if you use something that is unsupported. 
(See [Haskell language support](../../../plutus-tx/README.md#haskell-language-support)
for more details on what is supported.)

The key technique that the Plutus Platform uses is called *staged metaprogramming*. 
What that means is that the main Haskell program *generates* another program, 
in this case the Plutus Core program that will run on the blockchain. Plutus
Tx is the mechanism that we use to write those programs. But the fact that it
is just Haskell means that we can use all the same techinques we use in the
main program, and we can share types and defintions between the two.

## Writing basic PlutusTx programs

```haskell
-- Necessary language extensions for the Plutus Tx compiler to work.
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tutorial.PlutusTx where

-- Main Plutus Tx module
import Language.PlutusTx
-- Additional support for lifting
import Language.PlutusTx.Lift
-- Builtin functions
import Language.PlutusTx.Builtins

-- Used for examples
import Language.PlutusCore
import Language.PlutusCore.Pretty
import Language.PlutusCore.Quote
import Language.PlutusCore.Evaluation.CkMachine
import Data.Text.Prettyprint.Doc
```

Plutus Tx makes heavy use of Template Haskell. There are a few reasons for this:
- Template Haskell allows us to do work at compile time, which is when we do
  Plutus Tx compilation.
- The Plutus Tx compiler can't see the definitions of arbitrary functions. However,
  a Template Haskell "splice" is inserted into the program entirely, which allows
  us to see all the code that we need to see.
- It allows us to wire up the machinery that actually invokes the Plutus Tx compiler.

Consequently, many of the definitions we will see will be Template Haskell quotes.
A Template Haskell quote is introduced with the special brackets `[||` and `||]`,
and will have type `Q (TExp a)`. This means it represents an expression of
type `a`, which lives in the `Q` type of quotes. You can splice a definition with this
type into your program using the `$$` operator.

(There is also an abbreviation `TExpQ a` for `Q (TExp a)`, which avoids some parentheses.)

The key function we will use is the `compile` function. `compile` has type
`Q (TExp a) -> Q (TExp (CompiledCode a))`. What does this mean?
- `Q` and `TExp` we have already seen
- `CompiledCode a` is a compiled Plutus Core program corresponding to a Haskell program of type `a`
  
What this means is that `compile` lets you take a (quoted) Haskell program and turn it into a (quoted) Plutus
Core program, which you can then splice into the main program. This happens when you *compile* the main
Haskell program (since that's when Template Haskell runs).

If you know about staged metaprogramming already you may be confused. Shouldn't we be generating the Plutus
Core program at *runtime*, not at compile time? That would be convenient, but we need the
Haskell compiler to help us compile arbitrary Haskell, so we have do this at compile time. We will see
later that we *can* lift some values from Haskell to Plutus Core at runtime, and this turns out
to be enough to allow us to write programs that depend on runtime values.

To reiterate: `compile` takes a Template Haskell quote, so what you write inside the quote
is just normal Haskell.

Here's the most basic program we can write: one that just evaluates to the integer `1`.

The Plutus Core syntax will look unfamiliar. This is fine, since it is the "assembly language" 
and you won't need to inspect the output of the compiler. However, for the purposes of this tutorial 
it's instructive to look at it to get a vague idea of what's going on.

```haskell
{- |
>>> pretty $ getPlc integerOne
(program 1.0.0
  (con 8 ! 1)
)
-}
integerOne :: CompiledCode Int
integerOne = $$( -- The splice inserts the `Q (CompiledCode Int)` into the program
    -- compile turns the `Q Int` into a `Q (CompiledCode Int)`
    compile
        -- The quote has type `Q Int`
        [||
          -- We don't have unbounded integers in Plutus Core, so we have to pin
          -- down this numeric literal to an `Int` rather than an `Integer`
          (1 :: Int)
        ||])
```

We can see how the metaprogramming works here: the Haskell program `1` was
turned into a `CompiledCode Int` at compile time, which we spliced into our Haskell program,
and which we can then inspect at runtime to see the generated Plutus Core (or to put it
on the blockchain).

The most important thing to get comfortable with here is the pattern we saw in the first
example: a TH quote, wrapped in a call to `compile`, wrapped in a `$$` splice. This is 
how we write all of our Plutus Tx blocks.

Here's a slightly more complex program, namely the identity function on integers.

```haskell
{- |
>>> pretty $ getPlc integerIdentity
(program 1.0.0
  (lam ds [(con integer) (con 8)] ds)
)
-}
integerIdentity :: CompiledCode (Int -> Int)
integerIdentity = $$(compile [|| \(x:: Int) -> x ||])
```

So far, so familiar: we compiled a lambda into a lambda (the "lam").

## Functions and datatypes

You can also define functions locally to use inside your expression. At the moment you
*cannot* use functions that are defined outside the Plutus Tx expression.
You can, however, splice in TH quotes, which lets you define reusable functions.

```haskell
plusOne :: Int -> Int
plusOne x = x `addInteger` 1

functions :: CompiledCode Int
functions = $$(compile [||
    let
        plusOneLocal :: Int -> Int
        plusOneLocal x = x `addInteger` 1
        -- This won't work.
        -- nonLocalDoesntWork = plusOne 1
        localWorks = plusOneLocal 1
        -- You can of course bind this to a name, but for the purposes
        -- of this tutorial we won't since TH requires it to be in
        -- another module.
        thWorks = $$([|| \(x::Int) -> x `addInteger` 1 ||]) 1
    in localWorks `addInteger` thWorks
    ||])
```

Here we used the function `addInteger` from `Language.PlutusTx.Builtins`, 
which is mapped on the builtin integer addition in Plutus Core.

We can use normal Haskell datatypes and pattern matching freely:

```haskell
matchMaybe :: CompiledCode (Maybe Int -> Int)
matchMaybe = $$(compile [|| \(x:: Maybe Int) -> case x of
    Just n -> n
    Nothing -> 0
   ||])
```

Unlike functions, datatypes do not need to be defined inside the
expression, hence why we can use types like `Maybe` from the `Prelude`.
This works for your own datatypes too!

Here's a small example with a datatype of our own representing a potentially open-ended
end date.

```haskell
-- | Either a specific end date, or "never".
data EndDate = Fixed Int | Never

-- | Check whether a given time is past the end date.
pastEnd :: CompiledCode (EndDate -> Int -> Bool)
pastEnd = $$(compile [|| \(end::EndDate) (current::Int) -> case end of
    Fixed n -> n `lessThanEqInteger` current
    Never -> False
   ||])
```

## The Plutus Tx Prelude and Plutus Tx Builtins

The `Language.PlutusTx.Prelude` module contains TH versions of a number of
useful standard Haskell functions.

PlutusTx has some builtin types and functions available for working with primitive
data (integers and bytestrings), as well as a few special functions. These builtins 
are also exported as TH functions from the Plutus Tx prelude.

The `error` builtin deserves a special mention. `error` causes the transaction to abort when it is
evaluated, which is the way that validation failure is signaled.

## Lifting values

So far we've seen how to define pieces of code *statically* (when you compile your main
Haskell program), but you are
likely to want to do so *dynamically* (when you run your main Haskell program). For example, you
might be writing the body of a transaction to initiate a crowdfunding smart contract,
which would need to be parameterized by user input determining the size of the goal,
the campaign start and end times, etc.

You can do this by writing the static code as a *function*, and then passing an
argument at runtime by *lifting* it and then applying the two programs together. As a
very simple example, let's write an add-one function.

```haskell
addOne :: CompiledCode (Int -> Int)
addOne = $$(compile [|| \(x:: Int) -> x `addInteger` 1 ||])
```

Now, suppose we want to apply this to `4` at runtime, giving us a program that computes
to `5`. Well, we need to *lift* the argument (`4`) from Haskell to Plutus Core, and then
we need to apply the function to it.

```
{- |
>>> let program = addOneToN 4
>>> pretty program
(program 1.0.0
  [
    [
      (lam
        addInteger
        (fun [(con integer) (con 8)] (fun [(con integer) (con 8)] [(con integer) (con 8)]))
        (lam ds [(con integer) (con 8)] [ [ addInteger ds ] (con 8 ! 1) ])
      )
      { (builtin addInteger) (con 8) }
    ]
    (con 8 ! 4)
  ]
)
>>> pretty $ runCk program
(con 8 ! 5)
-}
addOneToN :: Int -> Program TyName Name ()
addOneToN n = (getPlc addOne) `applyProgram` unsafeLiftProgram n
```

`Program` is a real PLC program, extracted from the `CompiledCode` wrapper. In later
tutorials we'll see some higher-level functions that hide this from us.

We lifted the argument `n` using the `unsafeLiftProgram` function ("unsafe" because
we're ignoring any errors that might occur from lifting something that we don't support).
In order to use this, a type must have an instance of the `Lift` class. In
practice, you should generate these with the `makeLift` TH function from
`Language.PlutusTx.Lift`. Lifting makes it easy to use the same types both inside your
Plutus Tx program and in the external code that uses it.

The combined program applies the original compiled lambda to the lifted value
(notice that the lambda is a bit complicated now since we have compiled the addition
into a builtin). We've then used the CK evaluator for Plutus Core to evaluate
the program and check that the result was what we expected

Here's an example with our custom datatype. The output is the encoded version of `False`.

```haskell
makeLift ''EndDate

{- |
>>> let program = pastEndAt Never 5
>>> pretty $ runCk program
(abs
  out_Bool (type) (lam case_True out_Bool (lam case_False out_Bool case_False))
)
-}
pastEndAt :: EndDate -> Int -> Program TyName Name ()
pastEndAt end current =
    (getPlc pastEnd)
    `applyProgram`
    unsafeLiftProgram end
    `applyProgram`
    unsafeLiftProgram current
```
