# Constant application

## Motivation for typed built-ins

We need to apply a built-in function to several arguments, how do we do that?

As an example, let's pick the `addInteger` built-in whose interpretation is `(+)` and whose type is `all s. integer s -> integer s -> integer s`.

This is what I wrote as a first attempt:

```haskell
applyBuiltinAddInteger :: [Constant ()] -> Maybe ConstantApplicationResult
applyBuiltinAddInteger args = do
    let throwAppExc err = throw $ ConstantApplicationException err AddInteger args
    (a1, args') <- uncons args                                                                      -- [1]
    case a1 of                                                                                      -- [2]
        BuiltinInt _ n i ->
            (a2, args'') <- uncons args'                                                            -- [3]
            case a2 of                                                                              -- [4]
                BuiltinInt _ m j -> do
                    when (n /= m) . throwAppExc $ SizeMismatchApplicationError a1 a2                -- [5]
                    when (not $ null args'') . throwAppExc $ ExcessArgumentsApplicationError args'' -- [6]
                    let k = i + j                                                                   -- [7]
                    Just $ if checkBoundsInt n k                                                    -- [8]
                        then ConstantApplicationSuccess $ BuiltinInt () n k                         -- [9]
                        else ConstantApplicationFailure                                             -- [10]
                _                -> throwAppExc $ IllTypedApplicationError a2
        _                -> throwAppExc $ IllTypedApplicationError a1
```

Step by step:

 1. Extract the first argument from the list of arguments.
 2. Check that it's of the right type, namely `Int`. Throw `IllTypedApplicationError` otherwise.
 3. Extract the second argument from the list of arguments.
 4. Check that it's of the right type, namely `Int`. Throw `IllTypedApplicationError` otherwise.
 5. Check that sizes match (note how arguments to `addInteger` are indexed by the same `s`).
 6. Check that there are no excess arguments. We do this even when returning a term (a `boolean` for example) rather than a constant, because constant application is supposed to be computed as soon as there are enough arguments and because it is not clear what to do otherwise: we could evaluate further, but that's a separate task and doesn't belong here, or we could return a non-value which doesn't look great as well.
 7. Perform the actual computation. In this case just sum the two arguments.
 8. Check whether the result is in bounds which are determined by the size of the arguments.
 9. Return the resulting `Int` in case the check is successful.
 10. Report a failure otherwise.

Then we note that `mulInteger` is of the same type, so we can make `applyBuiltinAddInteger` slightly more abstract:

```haskell
applyBuiltinSizeIntIntInt
    :: BuiltinName -> (Integer -> Integer -> Integer) -> [Constant ()] -> Maybe ConstantApplicationResult
applyBuiltinSizeIntIntInt name op args = ...
```

But a function like `eqInteger : all s. integer s -> integer s -> boolean` does not have this type, hence we need to repeat the whole process but in a slighly different manner in order to define `applyBuiltinEqInteger` (or, more generally, `applyBuiltinSizeIntIntBool`). Things that can be messed up:

 1. A mismatch between a function and its interpretation, e.g. we can mistakenly treat `eqInteger` as `(*)` and no type signatures would help.
 2. A size mismatch. Functions like `intToByteString : all s0, s1. size s1 -> integer s0 -> bytestring s1` have several sizes in them and it's easy to accidentally check something wrong or not to check something necessary.
 3. And it's just a terrible practice to write the same thing over and over again, because you can change something in one place and forget to make the same change in another.

So instead of writing all this boilerplate we explicitly type built-ins and define interpretation over typed built-ins. Here is how typed built-ins look like:

```haskell
newtype SizeVar = SizeVar Int

data TypedBuiltinSized a where
    TypedBuiltinInt  :: TypedBuiltinSized Integer
    TypedBuiltinBS   :: TypedBuiltinSized BSL.ByteString
    TypedBuiltinSize :: TypedBuiltinSized Size

data TypedBuiltin a where
    TypedBuiltinSized :: SizeVar -> TypedBuiltinSized a -> TypedBuiltin a
    TypedBuiltinBool  :: TypedBuiltin Bool

data TypeScheme a where
    TypeSchemeBuiltin :: TypedBuiltin a -> TypeScheme a
    TypeSchemeArrow   :: TypeScheme a -> TypeScheme b -> TypeScheme (a -> b)
    TypeSchemeForall  :: (SizeVar -> TypeScheme a) -> TypeScheme a

data TypedBuiltinName a = TypedBuiltinName BuiltinName (TypeScheme a)
```

An immediate example:

```haskell

sizeIntIntInt :: TypeScheme (Integer -> Integer -> Integer)
sizeIntIntInt =
    TypeSchemeForall $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinInt)
```

Note how the `sizeIntIntInt` TypeScheme reflects the type of, say, `addInteger`:

 - `TypeSchemeForall $ \s -> ...` represents `all s. ...`
 - `TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinInt)` represents `integer s`
 - `TypeSchemeArrow` represents `(->)`

`TypeScheme` is a GADT indexed by the Haskell interpretation of a PLC type. In the example above the type of `addInteger` becomes `Integer -> Integer -> Integer` on the Haskell side. For another example, `intToByteString` looks like this:

```haskell
typedIntToByteString :: TypedBuiltinName (Natural -> Integer -> BSL.ByteString)
typedIntToByteString =
    TypedBuiltinName IntToByteString $
        TypeSchemeForall $ \s0 -> TypeSchemeForall $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized s0 TypedBuiltinInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinBS)
```

Having interpretation defined over `TypeScheme`s solves all the problems mentioned above:

 1. Types prevent us from interpreting `equalsInteger` as `(+)` -- this simply won't type check provided the type scheme of `equalsInteger` is written correctly. You still can confuse `addInteger` with `mulInteger`, though.
 2. Sizes are checked automatically. First time a size is encountered for some particular size variable during evaluation of a constant application, this size is memorized and all subsequent sizes that come from the same size variable are checked against that memorized size.
 3. No code duplication. The interpretation function is written once and for all. If you want to add a new primitive, you just supply a new `TypeScheme`.

`TypeScheme`s are much more readable than what was presented in the first snippet in this article and as such can be easily visually inspected, hence are less vulnerable to bugs. Besides, this way we have much less stuff to test.