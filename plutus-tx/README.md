# plutus-tx: PlutusTx Haskell support

This provides support for writing PlutusTx programs in Haskell using Template Haskell.

This package just provides support for PlutusTx, if you are looking for support for
writing smart contracts using PlutusTx, please look in `wallet-api`.

## Haskell language support

In general, most "straightforward" Haskell should work. More advanced features may
or may not work, depending on whether they rely on features of GHC Core that aren't
supported. Most syntactic language extensions should be fine, you may get into trouble
with more advanced type system extensions.

TODO: link to GitHub issues for planned items once we're using them.

Not supported, but support planned:
- Mutually recursive datatypes (support planned)
    - Self-recursive datatypes are supported
- Record selectors (support planned)
- Functions defined outside the PlutusTx expression

Not supported, and support not planned:
- Datatypes beyond simple "Haskell98" datatypes
    - GADTs, constrained constructors, etc.
- Abstract datatypes
- Numeric types other than `Int`
- Literal patterns
- Typeclasses
    - Some `Num`, `Eq`, and `Ord` methods on
      `Int` and `Bytestring` are supported specially.
- Anything involving coercions

## Tutorial

Let's write some code!

```haskell
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
module README where
import Language.PlutusTx.TH
import Language.PlutusTx.Lift
import Language.PlutusCore
import Language.PlutusCore.Pretty
import Language.PlutusCore.Quote
import Language.PlutusCore.Evaluation.CkMachine
import qualified Language.Haskell.TH as TH
import Data.Functor
```

### Writing basic PlutusTx programs

The `PlcCode` type is an opaque type which contains the serialized Plutus Core code
corresponding to a Haskell expression. The `plutus` function takes a typed Template Haskell
`Q (TExp a)`, for any a, and produces a `Q (TExp PlcCode)`, which we then
have to splice into our program.

The fact that `plutus` takes a TH quote means that what you write inside the quote
is *just normal Haskell* - there is no PlutusTx-specific syntax, and the PlutusTx compiler will
tell you if you use any Haskell features which are not supported.

Here's the most basic program we can write: one that just evaluates to the integer `1`.

```haskell
-- |
-- >>> prettyPlcDef $ getAst integerOne
-- (program 1.0.0
--   (con 8 ! 1)
-- )
integerOne :: PlcCode
-- We don't like unbounded integers in Plutus Core, so we have to pin
-- down that numeric literal to an `Int` not an `Integer`.
integerOne = $$(plutus [|| (1 :: Int) ||])
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
-- |
-- >>> prettyPlcDef $ getAst integerIdentity
-- (program 1.0.0
--   (lam ds [(con integer) (con 8)] ds)
-- )
integerIdentity :: PlcCode
integerIdentity = $$(plutus [|| \(x:: Int) -> x ||])
```

So far, so familiar: we compiled a lambda into a lambda.

You can also define functions locally to use inside your expression. At the moment you
*cannot* use functions that are defined outside the PlutusTx expression, although hopefully
this will be easier in future. You can, however, splice in TH quotes, which lets you define
some reusable components.

```haskell
plusOne :: Int -> Int
plusOne x = x + 1

functions :: PlcCode
functions = $$(plutus [||
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

TODO: when we store the PIR, start showing PIR at this stage (or earlier).

We can use normal Haskell datatypes and pattern matching freely:

```haskell
matchMaybe :: PlcCode
matchMaybe = $$(plutus [|| \(x:: Maybe Int) -> case x of
    Just n -> n
    Nothing -> 0
   ||])
```

This works for your own datatypes too! (See [Haskell language support](#haskell-language-support)
for some caveats.) Unlike functions, datatypes do not need to be defined inside the
expression, hence why we can use types like `Maybe` from the `Prelude`.

Here's a small example with a datatype of our own representing a potentially open-ended
end date.
```haskell
data EndDate = Fixed Int | Never

shouldEnd :: PlcCode
shouldEnd = $$(plutus [|| \(end::EndDate) (current::Int) -> case end of
    Fixed n -> n <= current
    Never -> False
   ||])
```

### Using PlutusTx builtins

PlutusTx has some builtin types and functions available, both for working with primitive
data (integers and bytestrings), and also for performing chain-specific operations.

The PlutusTx builtins are available via the `Language.PlutusTx.Builtins` module. You
shouldn't need to use the integer and bytestring builtins directly, these are mapped
to the corresponding Haskell operations on `Int` and lazy `ByteString` directly. However,
you may wish to use some of the others.

`error` deserves a special mention. `error` causes the transaction to abort when it is
evaluated, which is the way that validation failure is signalled.

### Lifting values

This is all very good for defining pieces of code *statically*, but you are
likely to want to *dynamically* produce Plutus Core programs. For example, you
might be writing the body of a transaction to initiate a crowdfunding smart contract,
which would need to be parameterized by user input determining the size of the goal,
the campaign start and end times, etc.

You can do this by writing the static code as a function, and then passing an
argument at runtime by *lifting* it and then applying the two programs together. As a
very simple example, let's write an add-one function.

```haskell
-- TODO: show PIR here too

-- |
-- >>> let program = addOneToN 4
-- >>> prettyPlcDef program
-- (program 1.0.0
--   [
--     [
--       (lam
--         addInteger
--         (fun [(con integer) (con 8)] (fun [(con integer) (con 8)] [(con integer) (con 8)]))
--         (lam ds [(con integer) (con 8)] [ [ addInteger ds ] (con 8 ! 1) ])
--       )
--       { (builtin addInteger) (con 8) }
--     ]
--     (con 8 ! 4)
--   ]
-- )

-- >>> prettyPlcDef $ runCk program
-- (con 8 ! 5)
addOneToN :: Int -> Program TyName Name ()
addOneToN n =
    let
        addOne = $$(plutus [|| \(x:: Int) -> x + 1 ||])
        -- TODO: This looks terrible
        arg = Program () (defaultVersion ()) (runQuote $ unsafeLiftPlc n)
    in (getAst addOne) `applyProgram` arg
```

Here we have lifted the Haskell value `4` into a Plutus Core term at runtime.
In order to do this, a type must have an instance of the `LiftPir` class. In
practice, you should generate these with the `makeLift` TH function from
`Laguage.PlutusTx.Lift`. This makes it easy to use the same types both inside your
PlutusTx program and in the external code that uses it.

The combined program just applies the compiled lambda to the lifted value
(notice that the lambda is a bit complicated now since we have compiled the addition
into a builtin). We've then used the CK evaluator for Plutus Core to evaluate
the program and check that the result was what we expected

Here's an example with our custom datatype. The mysterious output is the encoded version of `False`.

```haskell
makeLift ''EndDate

-- |
-- >>> let program = shouldEndAt Never 5
-- >>> prettyPlcDef $ runCk program
-- (abs
--   out_Bool (type) (lam case_True out_Bool (lam case_False out_Bool case_False))
-- )
shouldEndAt :: EndDate -> Int -> Program TyName Name ()
shouldEndAt end current =
    let
        -- TODO: This looks terrible
        endP = Program () (defaultVersion ()) (runQuote $ unsafeLiftPlc end)
        currentP = Program () (defaultVersion ()) (runQuote $ unsafeLiftPlc current)
    in (getAst shouldEnd) `applyProgram` endP `applyProgram` currentP
```

This is more or less all you need to get started - from here on it should mostly
be like writing normal Haskell.
