# Builtins

## Intro

Programming languages commonly have some form of [foreign function interface](https://en.wikipedia.org/wiki/Foreign_function_interface). The idea is that

1. you don't want to reimplement everything from the bottom up in a newly designed language. It makes much more sense to delegate certain computations to an existing tool where such computations already exist in optimized form, with tons of tests, etc
2. in particular, you certainly don't want to implement your own version of arithmetics (integers, addition, multiplication, etc) or any other low-level stuff as that doesn't have any chance of not being several orders of magnitude slower than built-in primitives

One obvious thing that we need for Plutus is efficient arithmetics. So we could directly add a code for the `Integer` type to the AST of Plutus types and `Integer` constants to the AST of Plutus terms, as well as a few built-in functions (`AddInteger`, `SubtractInteger`, `MultiplyInteger`, etc). That would look something like this:

```haskell
data BuiltinType
    = Integer

data Type
    = BuiltinType BuiltinType
    | <...>

data Constant
    = ConstantInteger Integer

data BuiltinFunction
    = AddInteger
    | SubtractInteger
    | MultiplyInteger
    | <...>

data Term
    = Constant
    | AppBuiltinFunction BuiltinFunction [Term]
    | <...>
```

Then during evaluation (assuming we have `eval : Term -> Term`) `BuiltinFun` gets mapped to the actual function that it represents and `Integer` constants simply get unwrapped from `ConstantInteger` and supplied to the function, which then reduces and its result gets lifted back to Plutus Core.

For example,

```haskell
eval $ AppBuiltinFunction AddInteger
    [ Constant $ ConstantInteger 1
    , Constant $ ConstantInteger 2
    ]
```

expands to

```haskell
hsToPlc (1 + 2)
```

which reduces to `Constant (ConstantInteger 3)`.

Then if you need more built-in types and functions you simply extend the `BuiltinType`, `Constant` and `BuiltinFunction` data types with new primitives.

This is a viable approach and it's what was originally implemented in Plutus Core, but it has a major downside of not being flexible:

1. you can't easily add a `trace` function to the set of built-in functions to debug some code and then remove it once the bug is found. With this setup adding `trace` requires tinkering with the AST and updating all of the main procedures (type checking, evaluation, pretty-printing, what have you), which is extremely tedious
2. more importantly, you can only have a single configuration of builtins. Given that Plutus is going to be run on different blockchains giving access to different primitives, it's not an option to have a hardcoded set of builtins. For example, privacy-preserving ledgers may restrict the kinds of computation that can be done, which may mean we only have some kinds of arithmetic operations.

So we had to make builtins extensible. Which amounts to making the `BuilinType`, `Constant` and `BuiltinFunction` data types extensible. The first two are about extensible types and the last one is about extensible functions, so we'll consider those things separately.

## Extensible types

There's a fairly standard technique used in the context of generic programming, especially within dependently typed systems, that allows to describe a (possibly infinite) set of types. [Quoting David Christiansen](https://groups.google.com/d/msg/idris-lang/N9_pVqG8dO8/mHlNmyL6AwAJ):

> <...> we have a pretty good way to pattern match on the sub-universe of types that you want to consider for some particular purpose: the universe pattern.
>
> Make a datatype that encodes the types you care about and an interpretation for these codes as types. For example, if I care about Nat and iterated Lists thereof, I might write:
>
> ```idris
> data U = NAT | LIST U
>
> el : U -> Type
> el NAT = Nat
> el (LIST t) = List (el t)
> ```
>
> and then I can do generic programming (that is, matching the type structure) as follows:
>
> ```idris
> toString : (t : U) -> el t -> String
> toString NAT Z = "zero"
> toString NAT (S k) = "s(" ++ toString NAT k ++ ")"
> toString (LIST t) [] = "nil"
> toString (LIST t) (x::xs) = "cons(" ++ toString t x ++ ", " ++ toString (LIST t) xs ++ ")"
> ```

Another reference is the [standard Agda tutorial](www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf), in particular its "3.2 Universes" section.

We can apply this technique in our setting. Even though Haskell lacks dependent types, it's possible to couple a tag for a type together with that type via a GADT:

```haskell
data U a where
    UUnit :: U ()
    UInt  :: U Int
```

`U` is a universe consisting of `UUnit` (a tag for `()`) and `UInt` (a tag for `Int`).

Another example is

```haskell
data U a where
    UBool :: U Bool
    UList :: !(U a) -> U [a]
```

which is a universe consisting of booleans, lists of booleans, lists of lists of booleans, etc. Here are some values of that universe / the types that they encode

```
UBool               / Bool
UList UBool         / [Bool]
UList (UList UBool) / [[Bool]]
```

Both `U`s are of kind `* -> *` and so if we want the AST of the language to be parameterized by a set of types, we need to parameterize it by a thing of type `* -> *`. Here's what we get (ignoring built-in functions for the moment):

```haskell
data SomeType uni = forall a. SomeType (uni a)

data Type uni
    = BuiltinType (SomeType uni)
    | <...>

data SomeValueIn uni = forall a. SomeValueIn (uni a) a

data Term uni
    = Constant (SomeValueIn uni)
    | <...>
```

So `BuiltinType` stores just a tag like before, since the actual Haskell type the tag corresponds to is ignored (`a` is bound existentially in `SomeType` and only used in `uni a`).

`Constant` now stores the tag of a type as well as a value of that that type.

The original hardcoded builtins can now be recovered as

```haskell
data U a where
    UInteger :: U Integer

pattern Integer = SomeType UInteger
pattern ConstantInteger = SomeValueIn UInteger

type OriginalType = Type U
type OriginalTerm = Term U
```

Now we can parameterize the AST by different universes of types. Of course, this requires support from all procedures (type checking, evaluation, etc) and every universe must implement a certain interface (see the [default universe](..//src/PlutusCore/Default/Universe.hs) for an example).

There are some technical difficulties on how to provide instances of various type classes for `SomeType` and `SomeValueIn`, how to make deriving work, etc (you can read about those in [source code of Plutus Core](..//src/Universe/Core.hs)), but otherwise this is pretty much the entire encoding.

Implemented in [this PR](https://github.com/input-output-hk/plutus/pull/1849).

## Extensible functions

There are two approaches for making built-in functions extensible:

1. instead of making `BuiltinFunction` an enumeration type, we can define it as

```haskell
newtype BuiltinFunction = BuiltinFunction Text
```

and provide a mapping from the name of a built-in function to its meaning, so that all relevant info is available during type checking and evaluation (we'll talk about meanings of builtins later)

2. parameterize `Term` over `fun` representing a set of built-in functions. Unlike with universes we don't need to establish an isomorphism with some actual Haskell type right in the AST, so it's just the direct

```haskell
data Term fun
    | AppBuiltinFunction fun [Term]
    | <...>
```

and the original `Term` can be recovered by

```haskell
-- The original definition.
data BuiltinFunction
    = AddInteger
    | SubtractInteger
    | MultiplyInteger
    | <...>

type OriginalTerm = Term BuiltinFunction
```

Those two representations are very similar. Differences:

- (2) requires adding another type variable, which can be annoying if you already have several of them (we do)
- (2) is more expressive: it allows to specify at the type level what built-in functions a term may reference. Those can be built-in functions from a certain set (including the empty one) or you can instantiate `fun` with `Text` and get an equivalent of (1)
- (1) requires adding another kind of errors: the name of a built-in function is not found in a mapping from built-in function names to their meanings during type checking or evaluation (not a big deal in practice)
- (1) requires to parameterize the parser by a set of names of built-in functions, while in (2) this set is determined from the type of the result

In general, differences are minor, so either of the approaches is fine. We use (2).

### Built-in function meaning

Even without extensible types and functions it's convenient to encode the type of a built-in function as a GADT to be able to handle all built-in functions uniformly by processing the structure of that GADT during evaluation to statically ensure well-typedness of applications of primitive functions to constants. We have a [separate (and a little outdated) doc](https://github.com/input-output-hk/plutus/blob/f9f81a441e29eeefc16546c4f3bc39e8614569eb/language-plutus-core/docs/Constant%20application.md) elaborating on that point.

With extensible builtins there's no way around having such a generic machinery allowing to describe a type of a primitive function, because much like with extensible types we need to establish a connection between a built-in function and its Haskell denotation, so we resort to juggling GADTs again. The crux of the encoding is as follows:

```haskell
-- @uni a@ as a constraint.
class uni `Includes` a where
    knownUni :: uni a

data TypeScheme uni (args :: [GHC.Type]) res where
    TypeSchemeResult
        :: uni `Includes` res
        => Proxy res -> TypeScheme uni '[] res
    TypeSchemeArrow
        :: uni `Includes` arg
        => Proxy arg -> TypeScheme uni args res -> TypeScheme uni (arg ': args) res

type family FoldArgs args res where
    FoldArgs '[]           res = res
    FoldArgs (arg ': args) res = arg -> FoldArgs args res

data BuiltinFunctionMeaning uni =
    forall args res. BuiltinFunctionMeaning
        (TypeScheme uni args res)
        (FoldArgs args res)
```

`TypeScheme` describes the type of a primitive function: its first argument is the list of types of arguments of that function and its second argument is the type of the result. E.g. `Char -> Bool -> Integer` gets encoded as

```haskell
charBoolInteger :: (uni `Includes` Char, uni `Includes` Bool) => TypeScheme uni [Char, Bool] Integer
charBoolInteger =
    Proxy @Char `TypeSchemeArrow`
    Proxy @Bool `TypeSchemeArrow`
    TypeSchemeResult (Proxy @Integer)
```

`FoldArgs` takes the list of types of arguments of a function and the type of the result and folds them back into the type of that function. E.g. `FoldArgs [Char, Bool] Integer` gives `Char -> Bool -> Integer` back.

Finally, `BuiltinFunctionMeaning` is just a `TypeScheme` of a primitive function and the primitive function itself (of type `FoldArgs args res`).

Then when we encounter `AppBuiltinFunction fun args` during evaluation we evaluate `fun` and look up its meaning in the provided environment of `BuiltinFunctionMeaning`s, which allows to retrieve a `TypeScheme`, as well as a Haskell function `f`. Having the `TypeScheme` we know what type each of `args` must have, so after evaluating them to constants we traverse that list of constants and check if the type tag of every constant is the same one as is currently expected from the `TypeScheme` info: if the tags match, then the types they represent must also match and the Haskell type checker sees that ('cause we're using GADTs), so we can type-safely apply `f` to a freshly obtained constant.

The `TypeScheme` of a built-in function also allows to get the Plutus Core type of that function: it's straightforward recursion on `TypeScheme` where each `TypeSchemeArrow` becomes `->` of the target language and each implicit ``uni `Includes` arg`` representing an argument becomes a `BuiltinType (SomeType uni)`, and ``uni `Includes` res`` representing the resulting type also becomes a `BuiltinType (SomeType uni)`.

So having a single `TypeScheme` is enough to adapt the type checker and the evaluator to extensible built-in functions.

## Failing built-in functions

Built-in functions are allowed to fail, e.g. `1/0` results in evaluation failure. This requires some straightforward support in `TypeScheme`. The ability of a function to fail is not reflected in its type signature, e.g. `DivideInteger` is of type `Integer -> Integer -> Integer`.

Built-in functions are currently not allowed to catch failures. This was allowed previously, but required non-trivial support in the evaluation machinery as well as in `TypeScheme`, so we dropped all of that, because we don't seem to need to catch failures with built-in functions and we can always add a special `catchError` primitive (as a separate entity like `error`) to the language to ensure we're not missing any important corner cases.

## Polymorphism

So far we've been talking only about monomorphic built-in types and functions, but we can actually support polymorphism.

We need polymorphic functions, because adding a data type like `Bool` to the universe requires adding its matching function to the set of built-in functions (so that booleans can be matched on, not just constructed) and the type of that function is

```
ifThenElse : all a. bool -> a -> a -> a
```

In theory, it's possible to associate Plutus Core `all` with Haskell `forall`, so that Plutus Core

```
constPlc : all a b. a -> b -> a
```

gets mapped to Haskell

```haskell
constHs :: forall a b. a -> b -> a
```

(see the ["Embedding F"](http://homepages.inf.ed.ac.uk/slindley/papers/embedding-f.pdf) paper for that), but in reality it's way too heavyweight of an encoding. Instead, we employ a very simple strategy and map `constPlc` to

```haskell
constHs :: Term -> Term -> Term
```

The idea is that we have parametricity in Haskell, so a function that is polymorphic in its argument can't inspect that argument in any way and so we never actually need to convert such an argument from Plutus Core to Haskell just to convert it back later without ever inspecting the value. Instead we can keep the argument intact and apply the Haskell function directly to the Plutus Core AST representing some value.

## Saturated vs unsaturated built-in functions

We have a [separate doc](./Saturatedness.md) on that.
