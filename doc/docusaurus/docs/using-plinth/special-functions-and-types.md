---
sidebar_position: 25
---

# Special Functions and Types

Normally, the Plinth compiler compiles a Haskell identifier by obtaining and compiling its definition (also known as unfolding), and creating a term binding in PIR, an intermediate representation used by the Plinth compiler.
Types are compiled in a similar manner, by compiling the type's definition and generating a type or datatype binding in PIR.

However, there are certain special functions and types that aren't compiled this way.
Rather, they are handled specially and directly converted to terms or types in PIR.
It is useful to be aware of these, as these functions and types work differently than regular user-defined functions and types, and cannot be defined in user space.

## Builtin Functions and Types

There are a number of builtin functions and builtin types in UPLC.
The list of builtin functions and types can be found in the [Plutus Core Specification](https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf).

In [`PlutusTx.Builtins.Internal`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins-Internal.html), functions marked `OPAQUE` are directly converted to the corresponding builtin function.
For instance, `PlutusTx.Builtins.Internal.addInteger` is converted to UPLC term `(builtin addInteger)`.
Using the `OPAQUE` pragma prevents GHC from inlining these functions, allowing the Plinth compiler to determine where exactly they are invoked, and compile them appropriately.

Builtin types are handled similarly: rather than compiling their definition, they are directly converted to builtin types in PIR.
In UPLC, most types are erased, but constants remain tagged with the corresponding builtin types.

Since functions in `PlutusTx.Builtins.Internal` correspond to builtin functions that operate on builtin types, it's usually preferable to use functions in [`PlutusTx.Builtins`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins.html).
These functions wrap their counterparts in the `Internal` module, and operate on standard Haskell types whenever possible, which are often more convenient.

Aside from `BuiltinInteger`, which is an alias for `Integer`, other builtin types are distinct from their corresponding Haskell types.
Not all of these Haskell types can be used in Plinth.
For instance, `String` and `ByteString` are not supported, whereas regular algebraic data types like `Bool`, lists and pairs are supported.

## `PlutusTx.Bool.&&` and `PlutusTx.Bool.||`

In [`PlutusTx.Bool`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Bool.html), the `&&` and `||` operators are handled specially in the plugin to ensure they can short-circuit.
In most strict languages, these operators are special and cannot be defined by users, which is also the case for Plinth.

Note that in regular Haskell, `&&` and `||` are _not_ special, as Haskell supports non-strict function applications (and it is the default behavior).

## `IsString` Instances

[`IsString`](https://hackage.haskell.org/package/base/docs/Data-String.html#t:IsString) is a type class from `base`, and can be used along with the `OverloadedStrings` language extension to convert string literals to types other than `String`.

> :pushpin: **NOTE**
>
> `String` and `ByteString` are not available in Plinth, so you'll need to use `BuiltinString` or `BuiltinByteString`.

This lets you write `"hello" :: BuiltinString` in Plinth, which is quite convenient.

### Builtin ByteString literals

Working with `BuiltinByteString` using `OverloadedStrings` requires care. For backward compatibility, an `IsString` instance exists for `BuiltinByteString`. This instance mirrors the standard Haskell `IsString ByteString` behavior: it converts each character to a byte by taking the lowest 8 bits of its Unicode code point.

However, its use is discouraged because this conversion is lossy, keeping only the lowest byte of each character's Unicode code point. This means that characters with Unicode code points above 255 (i.e., outside the Latin-1 range) will not be represented correctly, leading to potential data loss. The example below illustrates this truncation.
 
<details>
<summary>Example of lossy conversion</summary>
```haskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.ByteString as BS
import Data.Char (ord)
import Data.Bits ((.&.))

main = do
  print $ BS.unpack ("世" :: BS.ByteString)  -- [22]
  print $ ord '世'                           -- 19990
  print $ (19990 :: Integer) .&. 0xFF        -- 22 (truncation result)
```
</details>

Instead, Plinth provides encoding-specific newtypes, each with its own `IsString` instance. Currently, two encodings are supported:
- **Hexadecimal**, also known as **Base 16**, via the `BuiltinByteStringHex` newtype.
- **UTF-8** via the `BuiltinByteStringUtf8` newtype.

The newtypes are zero-cost abstractions that tell the compiler which `IsString` instance to use.
They can be converted to `BuiltinByteString` using the corresponding functions:

```haskell
unBuiltinByteStringHex :: BuiltinByteStringHex -> BuiltinByteString
unBuiltinByteStringUtf8 :: BuiltinByteStringUtf8 -> BuiltinByteString
```

Here are some usage examples:
```haskell
{-# LANGUAGE OverloadedStrings #-}

import PlutusTx.Builtins 
  ( BuiltinByteString
  , BuiltinByteStringUtf8
  , unBuiltinByteStringHex
  , unBuiltinByteStringUtf8
  )

aceOfBase16 :: BuiltinByteString
aceOfBase16 = unBuiltinByteStringHex "ACE0FBA5E"
-- ^ type inference figures out that the literal has 
-- the `BuiltinByteStringHex` type

nonLatinTokenName :: BuiltinByteString
nonLatinTokenName = 
  unBuiltinByteStringUtf8 
    ("Мой Клёвый Токен" :: BuiltinByteStringUtf8)
-- here we use an explicit ^^^ type annotation for the
-- `BuiltinByteStringUtf8` newtype 
```

:::tip
You do not need to convert a `BuiltinByteStringHex` or `BuiltinByteStringUtf8` value to `BuiltinByteString` immediately.
You can pass it around and only convert it when the context requires a `BuiltinByteString`.
This preserves the encoding information in the type and allows downstream code to rule out invalid states.
For example:
```haskell
hexBytes :: BuiltinByteStringHex
hexBytes = "AABBCCDD" 

numberOfBytes :: BuiltinByteStringHex -> Integer
numberOfBytes hex = lengthOfByteString (unBuiltinByteStringHex hex)
```
:::

As an alternative to the `OverloadedStrings` language extension, you can use special functions from the `PlutusTx.Builtins.HasOpaque` module:

```haskell 
import PlutusTx.Builtins.HasOpaque 
  ( stringToBuiltinByteStringHex
  , stringToBuiltinByteStringUtf8
  )

-- stringToBuiltinByteStringHex :: String -> BuiltinByteString

aceOfBase16 :: BuiltinByteString
aceOfBase16 = stringToBuiltinByteStringHex "ACE0FBA5E" 

-- stringToBuiltinByteStringUtf8 :: String -> BuiltinByteString

mother :: BuiltinByteString
mother = stringToBuiltinByteStringUtf8 "Мама"
```

These functions convert Haskell's `String` literal to Plinth's `BuiltinByteString` using the corresponding encoding.
What makes them special is that they are executed by Plinth **at compile time**, without increasing the size and execution budget of a Plinth program.

:::caution
These compile-time functions need to be *syntactically* applied to string literals, meaning that you cannot apply them to variables or expressions that are not string literals.
For example, the following code will not compile:

```haskell
stringToBuiltinByteStringHex ("ACE0F" ++ "BA5E")
```
:::
