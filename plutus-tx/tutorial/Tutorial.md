# Tutorial

```haskell
-- Necessary language extensions
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tutorial where

-- Main Plutus Tx module
import Language.PlutusTx
-- Additional support for lifting
import Language.PlutusTx.Lift

-- Used for examples
import Language.PlutusCore
import Language.PlutusCore.Pretty
import Language.PlutusCore.Quote
import Language.PlutusCore.Evaluation.CkMachine
```

## Writing basic PlutusTx programs

The `CompiledCode a` type is an opaque type which contains the serialized Plutus Core code
corresponding to a Haskell expression of type `a`. The `compile` function takes a typed Template Haskell
`Q (TExp a)`, for any a, and produces a `Q (TExp (CompiledCode a))`, which we then
have to splice into our program.

The fact that `compile` takes a TH quote means that what you write inside the quote
is *just normal Haskell* - there is no Plutus Tx-specific syntax, and the Plutus Tx compiler will
tell you if you use any Haskell features which are not supported.

Here's the most basic program we can write: one that just evaluates to the integer `1`.

```haskell
{- |
>>> pretty $ getPlc integerOne
(program 1.0.0
  (con 8 ! 1)
)
-}
integerOne :: CompiledCode Int
-- We don't like unbounded integers in Plutus Core, so we have to pin
-- down that numeric literal to an `Int` not an `Integer`.
integerOne = $$(compile [|| (1 :: Int) ||])
```

The Plutus Core program will look incomprehensible, which is fine, since you
mostly won't want to look at the output of the compiler. However, it's instructive to
look at it here just to get a vague idea of what's going on.

We can already see a few features of Plutus Core here:
- The program includes the *language version*. This ensures that we always know how to handle
  programs once they're on the chain.
- Integers have *sizes*, in this case 8 bytes (64 bits).

Both of these things are handled for us by the compiler.

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

So far, so familiar: we compiled a lambda into a lambda.

You can also define functions locally to use inside your expression. At the moment you
*cannot* use functions that are defined outside the Plutus Tx expression, although hopefully
this will be easier in future. You can, however, splice in TH quotes, which lets you define
reusable functions.

```haskell
plusOne :: Int -> Int
plusOne x = x + 1

functions :: CompiledCode Int
functions = $$(compile [||
    let
        plusOneLocal :: Int -> Int
        plusOneLocal x = x + 1
        -- This won't work.
        -- nonLocalDoesntWork = plusOne 1
        localWorks = plusOneLocal 1
        -- You can of course bind this to a name, but for the purposes
        -- of this tutorial we won't since TH requires it to be in
        -- another module.
        thWorks = $$([|| \(x::Int) -> x + 1 ||]) 1
    in localWorks + thWorks
    ||])
```

From this point on we're going to start dealing with more advanced features of
Haskell, like datatypes. The way these are encoded into Plutus Core is quite
tricky, so we're going to stop looking at the generated Plutus Core code, but
it's in there if you're curious.

We can use normal Haskell datatypes and pattern matching freely:

```haskell
{- |
>>> pretty $ getPir matchMaybe
(program
  (let
    (nonrec)
    (datatypebind
      (datatype
        (tyvardecl Maybe (fun (type) (type)))
        (tyvardecl a (type))
        Maybe_match
        (vardecl Just (fun a [Maybe a])) (vardecl Nothing [Maybe a])
      )
    )
    (lam
      ds
      [Maybe [(con integer) (con 8)]]
      [
        [
          {
            [ { Maybe_match [(con integer) (con 8)] } ds ]
            [(con integer) (con 8)]
          }
          (lam n [(con integer) (con 8)] n)
        ]
        (con 8 ! 0)
      ]
    )
  )
)
-}
matchMaybe :: CompiledCode (Maybe Int -> Int)
matchMaybe = $$(compile [|| \(x:: Maybe Int) -> case x of
    Just n -> n
    Nothing -> 0
   ||])
```

Here we've printed the Plutus IR for this program, instead of the Plutus Core. This is an
intermediary language that, unlike Plutus Core, has datatypes, so the output here is
a lot more readable, and we can see the definition of `Maybe` along with its constructors
and a pattern-matching function.

Unlike functions, datatypes do not need to be defined inside the
expression, hence why we can use types like `Maybe` from the `Prelude`.
This works for your own datatypes too! (See [Haskell language support](../README.md#haskell-language-support)
for some caveats.)

Here's a small example with a datatype of our own representing a potentially open-ended
end date.
```haskell
data EndDate = Fixed Int | Never

shouldEnd :: CompiledCode (EndDate -> Int -> Bool)
shouldEnd = $$(compile [|| \(end::EndDate) (current::Int) -> case end of
    Fixed n -> n <= current
    Never -> False
   ||])
```

## The Plutus Tx Prelude

The `Language.PlutusTx.Prelude` module contains TH versions of a number of
useful standard Haskell functions.

## Using Plutus Tx builtins

PlutusTx has some builtin types and functions available, both for working with primitive
data (integers and bytestrings), and also for performing chain-specific operations.

The PlutusTx builtins are available via the `Language.PlutusTx.Builtins` module. You
shouldn't need to use the integer and bytestring builtins directly, these are mapped
to the corresponding Haskell operations on `Int` and lazy `ByteString` directly. However,
you may wish to use some of the others.

`error` deserves a special mention. `error` causes the transaction to abort when it is
evaluated, which is the way that validation failure is signaled.

All the builtins that you will want to use in your programs are also re-exported from
the Plutus Tx Prelude as TH functions, so that you can have a
consistent usage style between your own reusable functions and builtin functions.

## Lifting values

This is all very good for defining pieces of code *statically*, but you are
likely to want to *dynamically* produce Plutus Core programs. For example, you
might be writing the body of a transaction to initiate a crowdfunding smart contract,
which would need to be parameterized by user input determining the size of the goal,
the campaign start and end times, etc.

You can do this by writing the static code as a function, and then passing an
argument at runtime by *lifting* it and then applying the two programs together. As a
very simple example, let's write an add-one function.

```haskell
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
addOneToN n =
    let addOne = $$(compile [|| \(x:: Int) -> x + 1 ||])
    in (getPlc addOne) `applyProgram` unsafeLiftProgram n
```

Here we have lifted the Haskell value `4` into a Plutus Core term at runtime.
In order to do this, a type must have an instance of the `Lift` class. In
practice, you should generate these with the `makeLift` TH function from
`Language.PlutusTx.Lift`. This makes it easy to use the same types both inside your
PlutusTx program and in the external code that uses it.

(The reason we're using the "unsafe" lift function is that we're not worrying about e.g. errors due to
unsupported Haskell features.)

The combined program just applies the compiled lambda to the lifted value
(notice that the lambda is a bit complicated now since we have compiled the addition
into a builtin). We've then used the CK evaluator for Plutus Core to evaluate
the program and check that the result was what we expected

Here's an example with our custom datatype. The mysterious output is the encoded version of `False`.

```haskell
makeLift ''EndDate

{- |
>>> let program = shouldEndAt Never 5
>>> pretty $ runCk program
(abs
  out_Bool (type) (lam case_True out_Bool (lam case_False out_Bool case_False))
)
-}
shouldEndAt :: EndDate -> Int -> Program TyName Name ()
shouldEndAt end current =
    (getPlc shouldEnd)
    `applyProgram`
    unsafeLiftProgram end
    `applyProgram`
    unsafeLiftProgram current
```

This is more or less all you need to get started - from here on it should mostly
be like writing normal Haskell.
