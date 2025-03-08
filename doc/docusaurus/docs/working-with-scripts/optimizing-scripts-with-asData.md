---
sidebar_position: 20
---

# Optimizing Scripts with `asData`

The Plutus libraries contain a `PlutusTx.asData` module that contains Template Haskell (TH) code for encoding algebraic data types (ADTs) as `Data` objects in Plutus Core, as opposed to sums-of-products terms.
In general, `asData` pushes the burden of a computation nearer to where a value is used, in a crude sense making the evaluation less strict and more lazy.
This is intended for expert Plutus developers.

## Purpose

Values stored in datums or redeemers need to be encoded into `Data` objects.
When writing and optimizing a Plutus script, one of the challenges is finding the right approach to handling `Data` objects and how expensive that method will be.
To make an informed decision, you may need to benchmark and profile your smart contract code to measure its actual resource consumption.
The primary purpose of `asData` is to give you more options for how you want to handle `Data`.

## Choice of two approaches

When handling `Data` objects, you have a choice of two pathways.
It is up to you to determine which pathway to use depending on your particular use case.
There are trade offs in performance and where errors occur.

### Approach one: proactively do all of the parsing

The first approach is to parse the object immediately (using `fromBuiltinData`) into a native Plutus Core datatype, which will also identify any problems with the structuring of the object.
However, this performs all the work up front.

This is the normal style that has been promoted in the past.

### Approach two: only do the parsing if and when necessary

In the second approach, the script doesn't do any parsing work immediately, and instead does it later, when it needs to.
It might be that this saves you a lot of work, because you may never need to parse the entire object.
Instead, the script will just carry the item around as a `Data` object.

Using this method, every time the script uses the object, it will look at it to find out if it has the right shape.
If it does have the right shape, it will deconstruct the `Data` object and do its processing; if
not, it will throw an error.
This work may be repeated depending on how your script is written.
In some cases, you might do less work, in some cases you might do more work, depending on your specific use case.

The Plinth library provides some helper types and functions to make this second style easier to do, in the form of the "data-backed" standard types and the `asData` function.

## `Data`-backed Plinth standard library

The Plinth standard library provides some common types which are already defined as `Data` objects under the hood.
We refer to such types as being _data-backed_.

- [PlutusTx.Data.List.List](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-tx/PlutusTx-Data-List.html#t:List), a data-backed version of the regular Plinth `[]` type.
- [PlutusTx.Data.AssocMap.Map](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-tx/PlutusTx-Data-AssocMap.html#t:Map), which is the data-backed version of `PlutusTx.AssocMap.Map`.

These types provide similar APIs to their regular Plinth counterparts.

There are also conversion functions between the two representations, and it is up to the developer to decide when or whether to convert to the regular representation or to use the data-backed API.
It depends on a case-by-case basis whether the data-backed or the regular versions perform the best.

It is, however, recommended to use them instead of the regular Plinth types when they are part of other types defined using `asData`.

## Using `asData`

The `asData` function takes the definition of a data type and replaces it with an equivalent definition whose representation uses `Data` directly.

For example, if we wanted to use it on the types from the [auction example](../auction-smart-contract/on-chain-code.md), we would put the datatype declarations inside a Template Haskell quote and call `asData` on it.

<LiteralInclude file="AuctionValidator.hs" language="haskell" title="" start="-- BLOCK9" end="-- BLOCK10" />

This is normal Template Haskell that just generates new Haskell source, so you can see the code that it generates with `{-# OPTIONS_GHC-ddump-splices #-}` but it will look something like this:

```
PlutusTx.asData
[d| data Bid'
        = Bid' {bBidder' :: PubKeyHash, bAmount' :: Lovelace}
        deriving newtype (Eq, Ord, ToBuitinData, FromBuiltinData, UnsafeFromBuiltinData)
    data AuctionRedeemer' = NewBid' Bid | Payout'
        deriving newtype (Eq, Ord, ToBuitinData, FromBuiltinData, UnsafeFromBuiltinData) |]

======>

newtype Bid' = Bid'2 BuiltinData
deriving newtype (Eq, Ord, PlutusTx.ToData, FromData, UnsafeFromData)

{-# COMPLETE Bid' #-}
pattern Bid' :: PubKeyHash -> Lovelace -> Bid'
pattern Bid' ...

newtype AuctionRedeemer' = AuctionRedeemer'2 BuiltinData
deriving newtype (Eq, Ord, PlutusTx.ToData, FromData, UnsafeFromData)

{-# COMPLETE NewBid', Payout' #-}
pattern NewBid' :: Bid -> AuctionRedeemer'
pattern NewBid' ...
pattern Payout' :: AuctionRedeemer'
pattern Payout' ...
```

That is:

- It creates a newtype wrapper around `BuiltinData`
- It creates pattern synonyms corresponding to each of the constructors you wrote

This lets you write code "as if" you were using the original declaration that you wrote, while in fact the pattern synonyms are handling conversion to/from `Data` for you.
But any values of this type actually are represented with `Data`.
That means that when we newtype-derive the instances for converting to and from `Data` we get
the instances for `BuiltinData` - which are free!

### Nested fields

The most important caveat to using `asData` is that `Data` objects encoding datatypes must also encode the *fields* of the datatype as `Data`.
However, `asData` tries to make the generated code a drop-in replacement for the original code, which means that when using the pattern synonyms they try to give you the fields as they were originally defined, which means *not* encoded as `Data`.

For example, in the `Bid` case above the `bAmount` field is originally defined to have type `Lovelace` which is a newtype around a Plutus Core builtin integer.
However, since we are using `asData`, we need to encode the field into `Data` in order to store it.
That means that when you construct a `Bid` object you must take the `Integer` that you start with and convert it to `Data`, and when you pattern match on a `Bid` object you do the reverse conversion.

These conversions are potentially expensive!
If the `bAmount` field was a complex data structure, then every time we constructed or deconstructed a `Bid` object we would need to convert that datastructure to or from `Data`.
Whether or not this is a problem depends on the precise situation, but in general:

- If the field is a builtin integer or bytestring or a wrapper around those, it is probably cheap
- If the field is a datatype which is itself defined with `asData` then it is free (since it's already `Data`)
- If the field is a list or a map, and are defined using the data-backed versions of list and map, then it is free
- If the field is any other kind of complex or large datatype, then it is potentially expensive

Therefore `asData` tends to work best when you use it for a type and also for all the types of its fields.

### Writing optimal code using `asData`

Consider the following type encoded using `asData`, and two functions which produce equivalent results:
```
PlutusTx.asData
    [d|
        data Point =
            Point
                { x :: Int
                , y :: Int
                , z :: Int
                }
    |]

foo1 :: Point -> Int
foo1 point = x point + y point

foo2 :: Point -> Int
foo2 Point {x, y} = x + y
```

The second function, `foo2`, matches on the `Point` argument using record patterns.
This ensures that both fields are extracted at the same time from the underlying `Data` object.
In `foo1`, which uses field accessors instead, this will only be the case if the compiler detects that `x point` and `y point` both contain a common subexpression which can be factored out.
Depending on this compiler optimisation is unreliable, therefore the approach illustrated in `foo2` is preferred.

## Choosing an approach

There are a number of tradeoffs to consider:

1. Plinth's datatypes are faster to work with and easier to optimize than `Data`, so if the resulting object is going to be processed in its entirety (or have parts of it repeatedly processed) then it can be better to parse it up-front.
2. If it is important to check that the entire structure is well-formed, then it is better to parse it up-front, since the conversion will check the entire structure for well-formedness immediately, rather than checking only the parts that are used when they are used.
3. If you do not want to use `asData` for the types of the fields, then it may be better to not use it at all in order to avoid conversion penalties at the use sites.

Which approach is better is an empirical question and may vary in different cases.
A single script may wish to use different approaches in different places.
For example, your datum might contain a large state object which is usually only inspected in part (a good candidate for `asData`), whereas your redeemer might be a small object which is inspected frequently to determine what to do (a good candidate for a native Plinth datatype).

## Data-backed `ScriptContext`

The [ScriptContext](ledger-language-version.md#scriptcontext) is one type which can massively benefit from the `asData` approach.

Plinth scripts receive information from the ledger in the form of a `BuiltinData` argument.
This argument can be very large, especially in the case of [V3](ledger-language-version.md#plutus-v3) scripts.
Therefore, upfront parsing of this `BuiltinData` object into a native Plinth datatype may sometimes constitute wasted effort if the script does not make use of most of the information inside the script context.
This effort translates into high evaluation fees which could be avoided if the script would parse only what it needs from the script context.

For this use-case, we provide a version of the ledger API in which the `ScriptContext` types are data-backed, i.e. they are defined using this `asData` approach, and so are all the types on which the script contexts depend on as fields.

The module naming scheme is as follows:

- the `PlutusLedgerApi/Data/` directory contains the data-backed versions of the top-level `V1`, `V2` and `V3` modules
- inside each of the `PlutusLedgerApi/Vn` directories, where `n` represents the language version number, there is a `Data/` directory with the data-backed versions of modules specific to each language version.

Using this version of the ledger API can be as simple as modifying the relevant imports; for example, importing [PlutusLedgerApi.Data.V3](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-Data-V3.html) instead of [PlutusLedgerApi.V3](https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3.html), and so on.

If your script is slightly more complex, and it operates on those fields of the script context which are represented as lists or maps, then you will need to also import the respective data-backed collection type from the Plinth standard library.

It is recommended to use record patterns to extract all necessary fields of the `ScriptContext` at the beginning of a function.
The reasoning behind this is briefly explained [above](#writing-optimal-code-using-asdata).
