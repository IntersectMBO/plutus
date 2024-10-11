---
sidebar_position: 25
---

# Encoding Data Types in UPLC

Untyped Plutus Core (UPLC) is a language based on untyped lambda calculus.
The AST does not offer explicit support for encoding data types, but there are several alternative methods that can be used.
Different surface languages and compilers may adopt different encoding methods.

## Scott Encoding

Scott encoding ([Wikipedia](https://en.wikipedia.org/wiki/Mogensen%E2%80%93Scott_encoding)) is the original method we adopted for the Plutus Tx compiler, when targeting Plutus Core 1.0.0.
It can be done in untyped lambda calculus, and any language that extends untyped lambda calculus, including UPLC.

As an example, consider the `These` type, a value of `These`, and a function that inspects a `These`:

```haskell
data These a b
  = This a
  | That b
  | These a b

x :: These Integer BuiltinString
x = These 1 "hello"

f :: These Integer BuiltinString -> Integer
f = \case
  This a -> a
  That b -> 42
  These a b -> a
```

In Scott encoding, `x` and `f` are encoded as

```
x = \this that these -> these 1 "hello"

f = \x -> x (\a -> a) (\b -> 42) (\a b -> a)
```

To illustrate a recursive data type, consider a value of `[Integer]` and the `head` and `tail` functions:


```haskell
xs :: [Integer]
xs = [1, 2, 3]

head :: [Integer] -> Integer
head xs = case xs of
  y : ys -> y
  [] -> 42

tail :: [Integer] -> [Integer]
tail xs = case xs of
  y : ys -> ys
  [] -> []
```

These are encoded in Scott encoding as

```
xs = let c y ys = \cons nil -> cons y ys
         n = \cons nil -> nil
      in c 1 (c 2 (c 3 n))

head = \xs -> xs (\y ys -> y) 42

tail = let n = \cons nil -> nil
        in \xs -> xs (\y ys -> ys) n
```

(There is no let-bindings in UPLC, but `let a = rhs in b` can be read as `(\a -> b) rhs`.)

A related method of encoding data types is Church encoding ([Wikipedia](https://en.wikipedia.org/wiki/Church_encoding)).
It is identical to Scott encoding for non-recursive data types, but differs for recursive data types.
The Church encoding of `xs` and `head` is:

```
xs = \c n -> c 1 (c 2 (c 3 n))

head = \xs -> xs (\y ys -> y) 42
```

However, `tail` is much more complex and less efficient with Church encoding compared to Scott encoding.
Intuitively, expressing `tail` on a Church-encoded list involves taking a term where `c` is applied a number of times, and producing a new term where `c` is applied one less time - not a trivial task.
This is also the case with many other operations on Church encoded values, which is the main reason Scott encoding is chosen over Church encoding in the Plutus Tx compiler.

In Typed Plutus Core (TPLC), Scott encoding requires the ability to represent recursive types, hence the existence of isorecursive types in TPLC.
Church encoding, on the other hand, can be done in plain System F, a non-Turing-complete subset of TPLC.

## Sums of Products

Sums of products (SOP) is a more direct way of encoding data types in UPLC and TPLC.
It requires adding two new kinds of AST nodes: `Case` and `Constr`.
`Constr i [arg]` represents a value obtained by applying the `i`th constructor of a data type to arguments `[arg]`.
`Case scrut [handler]` represents pattern matching on `scrut` (which must evaluate to a `Constr` term), invoking the appropriate handler depending on the constructor index.

In the `These` example above, `x` and `f` are encoded as


```
x = constr 2 [1, "hello"]

f = \x -> case x [(\a -> a), (\b -> 42), (\a b -> a)]
```

where 2 is the index of constructor `These`.

In the list example,

```
x = constr 0 [1, constr 0 [2, constr 0 [3, constr 1 []]]]

head = \xs -> case xs [(\y ys -> y), 42]

tail = \xs -> case xs [(\y ys -> ys), constr 1 []]
```

SOP is cheaper and results in smaller scripts compared to Scott encoding, since it involves fewer lambdas and applications.
This is true both in terms of constant factors and asymptotically.
For example, pattern matching on a data type with _k_ constructors costs _O(k)_ since it involves _k_ applications, whereas it incurs constant cost with SOP.

SOP is available as of Plutus Core 1.1.0, and is what the Plutus Tx compiler uses when targeting Plutus Core 1.1.0.
At the moment, Plutus Core 1.1.0 is only supported in Plutus V3 and cannot be used in V1 or V2.

## Data Objects

[Data](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-core/PlutusCore-Data.html#t:Data) is a builtin type in Untyped Plutus Core.
It is intended primarily for data interchange, specifically for encoding datums, redeemers, and script contexts.
Data makes it simpler to create datums and redeemers using various languages and tools, or even manually, which is much easier than constructing UPLC terms.

Data objects can be used to encode data types (though not as expressive as Scott encoding or SOP, since Data objects cannot contain functions).
However, as with other data serialization/interchange formats (e.g., JSON or Protobuf-generated types), writing business logic directly using Data objects is inefficient and cumbersome.
Instead, the standard practice is to validate the incoming data, turn it into proper, efficient domain types, operate on those domain types, and if necessary, convert them back to the serialization/interchange format at the end.

For UPLC, the proper domain type is Scott or SOP terms.
Thus a standard way of writing Plutus Tx is to immediately validate the incoming Data objects and turning them into Scott or SOP terms via `unsafeFromBuiltinData` (see [Plutus Ledger Language Version](../working-with-scripts/ledger-language-version.md)), before working with them.
Then, after all computation is done, convert the output datums back into Data objects if needed.

However, when it comes to Plutus scripts, working directly with Data can sometimes be beneficial, especially for scripts with simpler logic.
This is because script size and execution units (CPU and memory) are much scarcer resources for Plutus scripts compared to regular programs.
Since script arguments (datums, redeemers, script contexts) and output datums are encoded as Data objects, the overhead of converting the arguments and output to/from Scott/SOP terms can sometimes outweigh the benefits, especially for scripts with simple business logic.
In extreme scenarios where an argument isn’t even used, the validation and conversion process becomes entirely unnecessary.

Another benefits of Data objects is efficient equality checks.
While working with Data objects is generally slower than using Scott/SOP terms, equality checks can be faster due to the `equalsData` builtin function.

The optimal encoding method may vary for different types within the same script.
Generally speaking, the more a data type is used, the more advantageous it is to use Scott or SOP encoding, compared to manipulating Data objects directly, as the efficiency of Scott/SOP can justify the conversion overhead between Data and Scott/SOP.

When writing Plutus Tx, it is possible to have your data types encoded using Data objects, rather than Scott/SOP, by utilizing the `asData` mechanism.
For more details, see [Optimizing Scripts with asData](./optimizing-scripts-with-asData.md).

As for script context, we are actively working on a Data-encoded script context API, though it is still in development. In the absence of that, you can also interact with Data objects directly using builtin functions that operate on Data.
For example, the following function extracts the `ScriptInfo` field from Plutus V3's `ScriptContext`, which is its third field:


```haskell
import PlutusTx.Builtins.Internal qualified as BI

getScriptInfo :: BuiltinData -> BuiltinData
getScriptInfo scriptContext =
  let ds = BI.snd (BI.unsafeDataAsConstr scriptContext)
   in -- extract the third element of the list
      BI.head (BI.tail (BI.tail ds))
```

This is of course much less type safe compared to working with regular data types, so exercise caution.
