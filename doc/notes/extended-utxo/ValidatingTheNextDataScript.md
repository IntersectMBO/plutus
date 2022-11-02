# Validating the next data script

This document is a stub.

Related issues: [#426](https://github.com/input-output-hk/plutus/issues/426), [#488](https://github.com/input-output-hk/plutus/issues/488).

## Description

Jann writes:

> See this picture:
>
> ![picture](https://i.imgur.com/qDov5TY.jpg)
>
> When validating the green input we don't know the values of the transaction's pay-to-script data scripts, because all we can see is their serialised form (`ByteString`). But there may be situations where we need to know the values of some of the outputs, for example to verify that they are what we expect them to be.
>
> How would `serialise :: a -> ByteString` solve the problem? We could serialise the expected value and then compare that `ByteString` to the one in the transaction. But we couldn't do anything else with the new transaction's data scripts.
>
> Another way to think of this is as a record, like in the `vinyl` package. In the picture I linked to, the signature of the green output's validator is something like `Data -> Redeemer -> { hash1 :: S, hash3 :: T } -> ()` where the labels `hash1` and `hash3` refer to the transaction's outputs. So we should be able to run this script on any transaction that produces outputs to the `hash1` and `hash3` addresses, of types `S` and `T`.

Michael writes:

> The problem is how to give a validator script access to the data scripts attached to outputs of the pending transaction. The following are true:
>
> - There may be an arbitrary number of data scripts (since there may be an arbitrary number of transaction outputs.
> - Considered as Plutus Core programs, the data scripts may have arbitrary, different types.
> - The validator script should not have to know the types of all the outputs - it should be possible to have "extra" outputs that it doesn't care about.
>
> This means that we either need a way to pass a heterogeneous list of values with an arbitrary tail, or a way to cram the data scripts into homogeneous values.

Roman writes:

> So if we take a step back and think about this whole problem, then what we need is
>
>  - some kind of "recoverable" existential typing
>  - the ability to apply a well-typed function to an unordered set of tagged untyped elements, some of which may be redundant
>
> Have we seen something like this in the wild? Yes, this is options parsing!

I'd like to stress this again: the situation is very similar to options parsing. This simplifies the problem to something that we're already familiar with. Except normally with options parsing the programmer explicitly specifies how to parse data types and we just want to get a once-and-for-all solution.

## Possible solutions

### Serialization-deserialization

TBD

### Literally options parsing

Any kind of first-order data can be serialized *inside Plutus* to bytestring and then deserialized back *inside Plutus*. The deserializer is determined by the expected type of the term that the bytestring represents. The expected type is determined by the hash associated with the bytestring. I.e. it's like the name of an option determines how to read the value of the option.

This is not a once-and-for-all solution and it would be really tedious to implement this, so we want something better.

### `dynamic`

We can add the `dynamic` primitive type to the language and the following primitive functions:

```
toTyped : all a. a -> dynamic
getTyped : all a. dynamic -> maybe a
```

The former wraps a term of any type into a `dynamic` value and the latter calls our actual type checker and either returns the value stored inside the dynamic or nothing if the type checker reports an error.

The problem with this solution is that it allows to implement type-case, e.g. provided we have a function that reverses lists, we can implement a function that reverses all lists except those that contain integers (pseudocode)

```
reverse : all a. list a -> list a
reverse = ...

reverseNonIntegers : all a. list a -> list a
reverseNonIntegers xs =
    case getTyped {list integer} (toTyped {list a} xs) of
        nothing -> reverse xs
        just xs -> xs
```

This breaks parametricity and is weird. Besides, we also need to keep track of types during evaluation and can't just erase them. Calling the type checker during evaluation is also a funny thing.

### `cast`

Let's say we have this builtin function:

```
cast : all a b. a -> maybe b
```

It has this weird behavior: if `a` and `b` are definitionally the same, then `cast` is equal to `just`, otherwise it's equal to `const nothing`. We can't of course define such a function in Plutus Core, because it checks equality of types at runtime and we do not have a runtime representation of types, so we make `cast` a magic builtin.

Having this function, we can make transaction output to be of the following type (I'm ignoring the value restriction problem for now):

```
list (hash × (all b. maybe b))
```

(where `hash` is an appropriate instantiation of `bytestring`). Here is an example (in pseudosyntax):

```
txOutput : list (hash × (all b. maybe b))
txOutput =
    [ ("aaa", /\b -> cast {integer 1}    {b} (1!1)  )
    , ("bbb", /\b -> cast {unit}         {b} unitval)
    , ("ccc", /\b -> cast {bool -> bool} {b} not    )
    ]
```

And then we can do the option parsing thing. For example if you need to get the part of the transaction output that has hash "ccc" and type `bool -> bool`, you just look up "ccc", get

```
/\ b -> cast {bool -> bool} {b} not
```

and instantiate `b` with `bool -> bool`:

```
cast {bool -> bool} {bool -> bool} not
```

which computes to `just not` of type `maybe (bool -> bool)`.

This way we get homogeneous lists that contain heterogeneous values inside, which we can extract by supplying expected types of those values.

Note that `cast` is isomorphic to `dynamic`:

- we can represent `dynamic` as `all b. maybe` b and implement it using `cast`
- they seem equally powerful: we can implement `cast` as `fromDynamic . toDynamic`. But `cast` seems conceptually simpler

so all the same problems apply.

### Safe `cast`/`dynamic`

There is however what I believe is a safe version of the `cast`/`dynamic` approach (they are isomorphic, so I'll be calling them the same approach).

The reason why regular `cast`/`dynamic` breaks parametricity is because we're allowed to call `cast`/`dynamic` over an argument that has an open type (i.e. a type that contains free variables). This is what we do above in the `reverseNonIntegers` function. Once we forbid to use open types, control flow can't be affected by `cast`/`dynamic` during evaluation and no type-case is possible to implement. We still can write things like

```
case cast {integer} {bytestring} 1 of
    nothing  -> ...
	just one -> ...
```

but here everything we need in order to determine runtime control flow is known at compile time. This is like instance search in Haskell where runtime behavior of a program is affected by types, because they drive instance resolution, but the behavior is determined at compile time.

(In fact, I believe we can even allow open types and still get parametricity by introducing a special monad to handle what is normally called quoting, but we do not really need this power to complicate the language)

However we still have the problems of ensuring that types are closed and can be erased.

### `Typeable`

Both the above problems can be solved by using some runtime type representation. There are two possible approaches: an opaque type representation and a type representation defined in the language itself.

#### An opaque type representation

This is what Haskell has (`Data.Typeable`). So we add

```
-----------------
typeRep :: * -> *

a :: *    a Closed
-------------------------
typeRepSing a : typeRep a
```

and a builtin name like

```
checkTypeRepEq : all a b c. typeRep a -> typeRep b -> (b -> c) -> c -> a -> c
```

that calls `g : b -> c` over `x : a` if `a` has the same type representation as `b` or returns `z : c` otherwise.

There is a question of how `typeRep`s are supposed to look on the Haskell side and how we check them for equality, but it's pretty technical question and it's solvable (e.g. we can store plain normalized Plutus Core types).

In this setting `dynamic` can be defined as

```
dynamic = all c. (all a. typeRep a -> a -> c) -> c
```

#### An in-language type representation

That is going to be hard. The thing is, how do we reflect type binders at the term level? There are two options:

- use well-typed contexts and first-order variables. We're not in Agda and this is going to be hard
- use term-level binders, i.e. lambdas, i.e. a higher-order representation. But then how do we decide equality of type indices using such a representation? I guess only by instantiating lambdas in a first-order way, i.e. by falling back to 1. This is even more complicated than 1, because going from [P]HOAS to FOAS is very complicated in general.

##### PHOAS

Here is a tiny Agda model (not exactly parametric, but that is easily fixable):

```agda
{-# OPTIONS --type-in-type #-}

infixr 5 _⇒_
infixl 7 _∙_

record Name {K : Set} (a : K) : Set where
  constructor name

data Typeable : {K : Set} -> K -> Set₁ where
  Var : {K : Set} {a : K} -> Name a -> Typeable a
  _⇒_ : {a b : Set} -> Typeable a -> Typeable b -> Typeable (a -> b)
  All : {K : Set} {f : K -> Set} -> (∀ {a} -> Name a -> Typeable (f a)) -> Typeable (∀ a -> f a)
  Lam : {J K : Set} {f : J -> K} -> (∀ {a} -> Name a -> Typeable (f a)) -> Typeable (λ a -> f a)
  _∙_ : {J K : Set} {f : J -> K} {a : J} -> Typeable f -> Typeable a -> Typeable (f a)

idTypeable : Typeable ((A : Set) -> A -> A)
idTypeable = All λ A -> Var A ⇒ Var A

fmapTypeable : Typeable ((F : Set -> Set) (A B : Set) -> (A -> B) -> F A -> F B)
fmapTypeable =
  All λ F -> All λ A -> All λ B ->
    (Var A ⇒ Var B) ⇒ Var F ∙ Var A ⇒ Var F ∙ Var B
```

I do not think this is going anywhere, because

- we have quantification over kinds there
- we need some kind of builtin ObservationalTypeTheory-like equality in order to be able to use this

### A "cryptographic" solution

Manuel writes:

> I occurred to me that in addition to the ”type-based” solution to this problem, there is also a (for lack of a better word) ”cryptographic” solution. What I mean is that we have been discussing how to extend the type system to solve this problem, but we could also discuss how to provide assurance of the fidelity of some piece of data instead.
>
> If we want to embed not just the hash, but the actual value of its data script in each transaction output of the validated transaction, we run into the problems we discussed. Instead, we could just do with the hash (which has a known type) and require that all data scripts that the validator wants to inspect are embedded in the redeemer script (which is of a specific type expected by the validator).
>
> The redeemer expression is created by the same off-chain code that populates the transaction’s outputs with data scripts, so this code has access to the data scripts and can put them into the redeemer. There is just one caveat: how do we (= the validator) know that the off-chain code is not cheating and embedding one value into a data script and a different one into the redeemer pretending to the data script.
>
> One approach would be to compute the hash of the value purported to be the data script and to compare it with the hash of the data script of the desired output. This would bring us back to the discussion of serialising/hashing PLC in PLC, which is tricky, but maybe less problematic to introduce dynamic types.
>
> Additionally, we could add a new builtin `dataValue :: forall a. integer -> a`, which is a reference to the data script in the i-th output of the validated transaction. This looks a bit like a grab-data-script-and-perform-a-dynamic-cast operation, but I would propose to handle it exactly like validator-redeemer composition: just as we actually compose the validator and redeemer before type checking the whole lot, we can inline all data script in place of the `dataValue i` expressions *before* type checking the redeemer — i.e., `datavalue` isn’t actually a primitive, it is more like a macro. We perform macro expansion, and then, type checking. (As a result, the type system is not affected at all).
>
> This is a feature that is much weaker than having dynamic types, but it is sufficient for our purpose.
