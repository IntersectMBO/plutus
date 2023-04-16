-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Default.Builtins where

import PlutusPrelude

import PlutusCore.Builtin
import PlutusCore.Data
import PlutusCore.Default.Universe
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.ExBudgetStream
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty

import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Crypto.Ed25519 (verifyEd25519Signature_V1, verifyEd25519Signature_V2)
import PlutusCore.Crypto.Secp256k1 (verifyEcdsaSecp256k1Signature, verifySchnorrSecp256k1Signature)

import Codec.Serialise (serialise)
import Data.ByteString qualified as BS
import Data.ByteString.Hash qualified as Hash
import Data.ByteString.Lazy qualified as BSL
import Data.Char
import Data.Ix
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8', encodeUtf8)
import Flat hiding (from, to)
import Flat.Decoder
import Flat.Encoder as Flat
import Prettyprinter (viaShow)

-- See Note [Pattern matching on built-in types].
-- TODO: should we have the commonest built-in functions at the front to have more compact encoding?
-- | Default built-in functions.
--
-- When updating these, make sure to add them to the protocol version listing!
-- See Note [New builtins and protocol versions]
data DefaultFun
    -- Integers
    = AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | EqualsInteger
    | LessThanInteger
    | LessThanEqualsInteger
    -- Bytestrings
    | AppendByteString
    | ConsByteString
    | SliceByteString
    | LengthOfByteString
    | IndexByteString
    | EqualsByteString
    | LessThanByteString
    | LessThanEqualsByteString
    -- Cryptography and hashes
    | Sha2_256
    | Sha3_256
    | Blake2b_256
    | VerifyEd25519Signature  -- formerly verifySignature
    | VerifyEcdsaSecp256k1Signature
    | VerifySchnorrSecp256k1Signature
    -- Strings
    | AppendString
    | EqualsString
    | EncodeUtf8
    | DecodeUtf8
    -- Bool
    | IfThenElse
    -- Unit
    | ChooseUnit
    -- Tracing
    | Trace
    -- Pairs
    | FstPair
    | SndPair
    -- Lists
    | ChooseList
    | MkCons
    | HeadList
    | TailList
    | NullList
    -- Data
    -- See Note [Pattern matching on built-in types].
    -- It is convenient to have a "choosing" function for a data type that has more than two
    -- constructors to get pattern matching over it and we may end up having multiple such data
    -- types, hence we include the name of the data type as a suffix.
    | ChooseData
    | ConstrData
    | MapData
    | ListData
    | IData
    | BData
    | UnConstrData
    | UnMapData
    | UnListData
    | UnIData
    | UnBData
    | EqualsData
    | SerialiseData
    -- Misc monomorphized constructors.
    -- We could simply replace those with constants, but we use built-in functions for consistency
    -- with monomorphic built-in types. Polymorphic built-in constructors are generally problematic,
    -- See note [Representable built-in functions over polymorphic built-in types].
    | MkPairData
    | MkNilData
    | MkNilPairData
    -- BLS12_381 operations
    -- G1
    | Bls12_381_G1_add
    | Bls12_381_G1_neg
    | Bls12_381_G1_scalarMul
    | Bls12_381_G1_equal
    | Bls12_381_G1_hashToGroup
    | Bls12_381_G1_compress
    | Bls12_381_G1_uncompress
    -- G2
    | Bls12_381_G2_add
    | Bls12_381_G2_neg
    | Bls12_381_G2_scalarMul
    | Bls12_381_G2_equal
    | Bls12_381_G2_hashToGroup
    | Bls12_381_G2_compress
    | Bls12_381_G2_uncompress
    -- Pairing
    | Bls12_381_millerLoop
    | Bls12_381_mulMlResult
    | Bls12_381_finalVerify

    deriving stock (Show, Eq, Ord, Enum, Bounded, Generic, Ix)
    deriving anyclass (NFData, Hashable, PrettyBy PrettyConfigPlc)

{- Note [Textual representation of names of built-in functions]. The plc parser
 parses builtin names by looking at an enumeration of all of the built-in
 functions and checking whether the given name matches the pretty-printed name,
 obtained using the instance below.  Thus the definitive forms of the names of
 the built-in functions are obtained by applying the function below to the
 constructor names above. -}
instance Pretty DefaultFun where
    pretty fun = pretty $ case show fun of
        ""    -> ""  -- It's really weird to have a function's name displayed as an empty string,
                     -- but if it's what the 'Show' instance does, the user has asked for it.
        c : s -> toLower c : s

instance ExMemoryUsage DefaultFun where
    memoryUsage _ = singletonRose 1

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

{- Note [Constants vs built-in functions]
A constant is any value of a built-in type. For example, 'Integer' is a built-in type, so anything
of type 'Integer' is a constant.

On the contrary a built-in function can't be of a built-in type, because the type of a built-in
function is always of either the @all a. b@ form or the @a -> b@ one, none of which is a built-in
type. This is checked by the machinery, so if the user tries to add a built-in function that is not
of one of these forms, they'll get a nice custom type error.

A built-in function is associated with its Haskell implementation: there can be many built-in
functions of the same type, all doing different things, and there can be infinitely more _definable_
built-in functions of the same type that are not built-in functions nonetheless, because we didn't
register them as such by providing a Haskell implementation for each of them. This is the difference
between constants and built-in functions: the set of constants (infinite in our case) depends solely
on the set of available built-in types (also infinite in our case, because we have @Integer@,
@[Integer]@, @[[Integer]]@ etc), while the set of built-in functions is defined by explicitly
assigning each member a specific name and an associated with it Haskell implementation. It is
theoretically possible to have an infinite set of built-in functions, but we neither do that nor
need it, hence our set of built-in functions is finite.

The rule of thumb is: constants are raw data and built-in functions are, well, functions.

@(:)@ works as follows: it takes two constants wrapped as values, extracts an integer from the first
constant and a list of integers from the second one, prepends the former to the latter and wraps the
resulting list back into a constant, which gets wrapped into a value.

Why does @(:)@ have to be a built-in function? Because its type is

    all a. a -> list a -> list a

and if we tried to make @(:)@ a constant we'd have to somehow make this type a built-in type and
promise that every value (i.e. every definable function) of this type can be used as a Plutus term,
which doesn't make any sense. Only the particular Haskell implementation that prepends an element to
a list is what we're interested in.

Why may @[]@ not be a built-in function? If its type is hardcoded to @[Integer]@, then that's a
built-in type and we know that anything of a built-in type can be embedded into a term as a
constant. I.e. @[] :: [Integer]@ is perfectly fine as a constant and does not need to be a built-in
function.

Why may @[]@ be a built-in function? If it's polymorphic over the type of the elements, then its
Plutus Core type is @all a. list a@ and that is not a built-in type, hence we have to make that a
built-in function.
-}

{- Note [How to add a built-in function: simple cases]
This Notes explains how to add a built-in function and how to read definitions of existing built-in
functions. It does not attempt to explain why things the way they are, that is explained in comments
in relevant files (will have a proper overview doc on that, but for now you can check out this
comment: https://github.com/input-output-hk/plutus/issues/4306#issuecomment-1003308938).

In order to add a new built-in function one needs to add a constructor to 'DefaultFun' and handle
it within the @ToBuiltinMeaning uni DefaultFun@ instance like this:

    toBuiltinMeaning <Name> =
        makeBuiltinMeaning
            <denotation>
            <costingFunction>

'makeBuiltinMeaning' creates a Plutus builtin out of its denotation (i.e. Haskell implementation)
and a costing function for it. Once a builtin is added, its Plutus type is kind-checked and printed
to a golden file automatically (consult @git status@).

Below we will enumerate what kind of denotations are accepted by 'makeBuiltinMeaning' without
touching any costing stuff.

1. The simplest example of an accepted denotation is a monomorphic function that takes values of
built-in types and returns a value of a built-in type as well. For example

    encodeUtf8 :: Text -> BS.ByteString

You can feed 'encodeUtf8' directly to 'makeBuiltinMeaning' without specifying any types:

    toBuiltinMeaning EncodeUtf8 =
        makeBuiltinMeaning
            encodeUtf8
            <costingFunction>

This will add the builtin, the only two things that remain are implementing costing for this
builtin (out of the scope of this Note) and handling it within the @Flat DefaultFun@ instance
(see Note [Stable encoding of PLC]).

2. If the type of the denotation has any constrained type variables in it, all of them need to be
instantiated. For example feeding @(+)@ directly to 'makeBuiltinMeaning' will give you an error
message asking to instantiate constrained type variables, which you can do via an explicit type
annotation or type application or using any other way of specifying types.

Here's how it looks with a type application instantiating the type variable of @(+)@:

    toBuiltinMeaning AddInteger =
        makeBuiltinMeaning
            ((+) @Integer)
            <costingFunction>

Or we can specify the whole type of the denotation by type-applying 'makeBuiltinMeaning':

    toBuiltinMeaning AddInteger =
        makeBuiltinMeaning
            @(Integer -> Integer -> Integer)
            (+)
            <costingFunction>

Or we can simply annotate @(+)@ with its monomorphized type:

    toBuiltinMeaning AddInteger =
        makeBuiltinMeaning
            ((+) :: Integer -> Integer -> Integer)
            <costingFunction>

All of these are equivalent.

It works the same way for a built-in function that has monomorphized polymorphic built-in types in
its type signature, for example:

    toBuiltinMeaning SumInteger =
        makeBuiltinMeaning
            (sum :: [Integer] -> Integer)
            <costingFunction>

3. Unconstrained type variables are fine, you don't need to instantiate them (but you may want to if
you want some builtin to be less general than what Haskell infers for its denotation). For example

    toBuiltinMeaning IfThenElse =
        makeBuiltinMeaning
            (\b x y -> if b then x else y)
            <costingFunction>

works alright. The inferred Haskell type of the denotation is

    forall a. Bool -> a -> a -> a

whose counterpart in Plutus is

    all a. bool -> a -> a -> a

and unsurprisingly it's the exact Plutus type of the added builtin.

It may seem like getting the latter from the former is entirely trivial, however
'makeBuiltinMeaning' jumps through quite a few hoops to achieve that and below we'll consider those
of them that are important to know to be able to use 'makeBuiltinMeaning' in cases that are more
complicated than a simple monomorphic or polymorphic function. But for now let's talk about a few
more simple cases.

4. Certain types are not built-in, but can be represented via built-in ones. For example, we don't
have 'Int' as a built-in, but we have 'Integer' and we can represent the former in terms of the
latter. The conversions between the two types are handled by 'makeBuiltinMeaning', so that the user
doesn't need to write them themselves and can just write

    toBuiltinMeaning LengthOfByteString =
        makeBuiltinMeaning
            BS.length
            <costingFunction>

directly (where @BS.length :: BS.ByteString -> Int@).

Note however that while it's always safe to convert an 'Int' to an 'Integer', doing the opposite is
not safe in general, because an 'Integer' may not fit into the range of 'Int'. For this reason

    YOU MUST NEVER USE 'fromIntegral' AND SIMILAR FUNCTIONS THAT CAN SILENTLY UNDER- OR OVERFLOW
    WHEN DEFINING A BUILT-IN FUNCTION

For example defining a builtin that takes an 'Integer' and converts it to an 'Int' using
'fromIntegral' is not allowed under any circumstances and can be a huge vulnerability.

It's completely fine to define a builtin that takes an 'Int' directly, though. How so? That's due
to the fact that the builtin application machinery checks that an 'Integer' is in the bounds of
'Int' before doing the conversion. If the bounds check succeeds, then the 'Integer' gets converted
to the corresponding 'Int', and if it doesn't, then the builtin application fails.

For the list of types that can be converted to/from built-in ones look into the file with the
default universe. If you need to add a new such type, just copy-paste what's done for an existing
one and adjust.

Speaking of builtin application failing:

5. A built-in function can fail. Whenever a builtin fails, evaluation of the whole program fails.
There's a number of ways a builtin can fail:

- as we've just seen a type conversion can fail due to an unsuccessful bounds check
- if the builtin expects, say, a 'Text' argument, but gets fed an 'Integer' argument
- if the builtin expects any constant, but gets fed a non-constant
- if its denotation runs in the 'EvaluationResult' and an 'EvaluationFailure' gets returned

Most of these are not a concern to the user defining a built-in function (conversions are handled
within the builtin application machinery, type mismatches are on the type checker and the person
writing the program etc), however explicitly returning 'EvaluationFailure' from a builtin is
something that happens commonly.

One simple example is a monomorphic function matching on a certain constructor and failing in all
other cases:

    toBuiltinMeaning UnIData =
        makeBuiltinMeaning
            (\case
                I i -> EvaluationSuccess i
                _   -> EvaluationFailure)
            <costingFunction>

The inferred type of the denotation is

    Data -> EvaluationResult Integer

and the Plutus type of the builtin is

    data -> integer

because the error effect is implicit in Plutus.

Returning @EvaluationResult a@ for a type variable @a@ is also fine, i.e. it doesn't matter whether
the denotation is monomorphic or polymorphic w.r.t. failing.

But note that

    'EvaluationResult' MUST BE EXPLICITLY USED FOR ANY FAILING BUILTIN AND THROWING AN EXCEPTION
    VIA 'error' OR 'throw' OR ELSE IS NOT ALLOWED AND CAN BE A HUGE VULNERABILITY. MAKE SURE THAT
    NONE OF THE FUNCTIONS THAT YOU USE TO DEFINE A BUILTIN THROW EXCEPTIONS

An argument of a builtin can't have 'EvaluationResult' in its type -- only the result.

6. A builtin can emit log messages. For that it needs to run in the 'Emitter' monad. The ergonomics
are the same as with 'EvaluationResult': 'Emitter' can't appear in the type of an argument and
polymorphism is fine. For example:

    toBuiltinMeaning Trace =
        makeBuiltinMeaning
            (\text a -> a <$ emit text)
            <costingFunction>

The inferred type of the denotation is

    forall a. Text -> a -> Emitter a

and the Plutus type of the builtin is

    all a. text -> a -> a

because just like with the error effect, whether a function logs anything or not is not reflected
in its type.

'makeBuiltinMeaning' allows one to nest 'EvaluationResult' inside of 'Emitter' and vice versa,
but as always nesting monads inside of each other without using monad transformers doesn't have good
ergonomics, since computations of such a type can't be chained with a simple @(>>=)@.

This concludes the list of simple cases. Before we jump to the hard ones, we need to talk about how
polymorphism gets elaborated, so read Note [Elaboration of polymorphism] next.
-}

{- Note [Elaboration of polymorphism]
In Note [How to add a built-in function: simple cases] we defined the following builtin:

    toBuiltinMeaning IfThenElse =
        makeBuiltinMeaning
            (\b x y -> if b then x else y)
            <costingFunction>

whose inferred Haskell type is

    forall a. Bool -> a -> a -> a

The way 'makeBuiltinMeaning' handles such a type is by traversing it and instantiating every type
variable. What a type variable gets instantiated to depends on where it appears. When the entire
type of an argument is a single type variable, it gets instantiated to @Opaque val VarN@ where
@VarN@ is pseudocode for "a Haskell type representing a Plutus type variable with 'Unique' N"
For the purpose of this explanation it doesn't matter what @VarN@ actually is and the representation
is subject to change anyway. 'Opaque' however is more fundamental and so we need to talk about it.
Here's how it's defined:

    newtype Opaque val (rep :: GHC.Type) = Opaque
        { unOpaque :: val
        }

I.e. @Opaque val rep@ is a wrapper around @val@, which stands for the type of value that an
evaluator uses (the builtins machinery is designed to work with any evaluator and different
evaluators define their type of values differently, for example 'CkValue' if the type of value for
the CK machine). The idea is simple: in order to apply the denotation of a builtin expecting, say,
an 'Integer' constant we need to actually extract that 'Integer' from the AST of the given value,
but if the denotation is polymorphic over the type of its argument, then we don't need to extract
anything, we can just pass the AST of the value directly to the denotation (which means the value
doesn't have to be a 'Constant', it can be completely arbitrary). I.e. in order for a polymorphic
function to become a monomorphic denotation (denotations are always monomorpic) all type variables
in the type of that function need to be instantiated at the type of value that a given evaluator
uses.

If we used just @val@ rather than @Opaque val rep@, we'd specialize

    forall a. Bool -> a -> a -> a

to

    Bool -> val -> val -> val

however then we'd need to separately specify the Plutus type of this builtin, since we can't infer
it from all these @val@s in the general case, for example does

    val -> val -> val

stand for

    all a. a -> a -> a

or

    all a b. a -> b -> a

or something else?

So we use the @Opaque val rep@ wrapper, which is basically a @val@ with a @rep@ attached to it where
@rep@ represents the Plutus type of the argument/result, which is how we arrive at

    Bool -> Opaque val Var0 -> Opaque val Var0 -> Opaque val Var0

Not only does this encoding allow us to specify both the Haskell and the Plutus types of the
builtin simultaneously, but it also makes it possible to infer such a type from a regular
polymorphic Haskell function (how that is done is a whole another story), so that we don't even need
to specify any types when creating built-in functions out of simple polymorphic denotations.

If we wanted to specify the type explicitly, we could do it like this (leaving out the @Var0@ thing
for the elaboration machinery to figure out):

    toBuiltinMeaning IfThenElse =
        makeBuiltinMeaning
            @(Bool -> Opaque val _ -> Opaque val _ -> Opaque val _)
            (\b x y -> if b then x else y)
            <costingFunction>

and it would be equivalent to the original definition. We didn't do that, because why bother if
the correct thing gets inferred anyway.

Another thing we could do is define an auxiliary function with a type signature and explicit
'Opaque' while still having explicit polymorphism:

    ifThenElse :: Bool -> Opaque val a -> Opaque val a -> Opaque val a
    ifThenElse b x y = if b then x else y

    toBuiltinMeaning IfThenElse =
        makeBuiltinMeaning
            ifThenElse
            <costingFunction>

This achieves the same, but note how @a@ is now an argument to 'Opaque' rather than the entire type
of an argument. In order for this definition to elaborate to the same type as before @a@ needs to be
instantiated to just @Var0@, as opposed to @Opaque val Var0@, because the 'Opaque' part is
already there, so this is what the elaboration machinery does.

So regardless of which method of defining 'IfThenElse' we choose, the type of its denotation gets
elaborated to the same

    Bool -> Opaque val Var0 -> Opaque val Var0 -> Opaque val Var0

which then gets digested, so that we can compute what Plutus type it corresponds to. The procedure
is simple: collect all distinct type variables, @all@-bind them and replace the usages with the
bound variables. This turns the type above into

    all a. bool -> a -> a -> a

which is the Plutus type of the 'IfThenElse' builtin.

It's of course allowed to have multiple type variables, e.g. in the following snippet:

    toBuiltinMeaning Const =
        makeBuiltinMeaning
            Prelude.const
            <costingFunction>

the Haskell type of 'const' gets inferred as

    forall a b. a -> b -> a

and the elaboration machinery turns that into

    Opaque val Var0 -> Opaque val Var1 -> Opaque val Var0

The elaboration machinery respects the explicitly specified parts of the type and does not attempt
to argue with them. For example if the user insisted that the instantiated type of 'const' had
@Var0@ and @Var1@ swapped:

    Opaque val Var1 -> Opaque val Var0 -> Opaque val Var1

the elaboration machinery wouldn't make a fuss about that.

As a final simple example, consider

    toBuiltinMeaning Trace =
        makeBuiltinMeaning
            (\text a -> a <$ emit text)
            <costingFunction>

from [How to add a built-in function: simple cases]. The inferred type of the denotation is

    forall a. Text -> a -> Emitter a

which elaborates to

    Text -> Opaque val Var0 -> Emitter (Opaque val Var0)

Elaboration machinery is able to look under 'Emitter' and 'EvaluationResult' even if there's a type
variable inside that does not appear anywhere else in the type signature, for example the inferred
type of the denotation in

    toBuiltinMeaning ErrorPrime =
        makeBuiltinMeaning
            EvaluationFailure
            <costingFunction>

is

    forall a. EvaluationResult a

which gets elaborated to

    EvaluationResult (Opaque val Var0)

from which the final Plutus type of the builtin is computed:

    all a. a

Read Note [How to add a built-in function: complicated cases] next.
-}

{- Note [How to add a built-in function: complicated cases]
Now let's talk about more complicated built-in functions.

1. In Note [Elaboration of polymorphism] we saw how a Haskell type variable gets elaborated to an
@Opaque val VarN@ and we learned that this type can be used directly as opposed to being inferred.
However there exist more ways to use 'Opaque' explicitly. Here's a simple example:

    toBuiltinMeaning IdAssumeBool =
        makeBuiltinMeaning
            (Prelude.id :: Opaque val Bool -> Opaque val Bool)
            <costingFunction>

This creates a built-in function whose Plutus type is

    id : bool -> bool

i.e. the Plutus type signature of the built-in function is the same as with

    toBuiltinMeaning IdBool =
        makeBuiltinMeaning
            (Prelude.id :: Bool -> Bool)
            <costingFunction>

but the two evaluate differently: the former takes a value and returns it right away while the
latter takes a value, extracts a 'Bool' constant out of it and then lifts that constant back into
@val@. The difference is not only in performance (obviously returning something right away is
cheaper than unlifting-then-lifting-back), but also in semantics: the former returns its argument
during evaluation regardless of what that argument is, so if someone generates Untyped Plutus Core
directly, they can apply @IdAssumeBool@ to a term that doesn't evaluate to a 'Bool' constant or
even a constant at all and that won't be a runtime error, while the latter has to be applied to
a term evaluating to a 'Bool' constant in order not to fail at runtime.

2. @val@ in @Opaque val rep@ is not completely arbitrary, it has to implement 'HasConstant', which
makes it possible to unlift @val@ as a constant or lift a constant back into @val@. There's a
'HasConstant' instance for @Opaque val rep@ whenever there's one for @val@, so if we, for some
reason, wanted to have 'Opaque' in the type signature of the denotation, but still unlift the
argument as a 'Bool', we could do that:

    toBuiltinMeaning IdAssumeCheckBool =
        makeBuiltinMeaning
            idAssumeCheckBoolPlc
            <costingFunction>
      where
        idAssumeCheckBoolPlc :: Opaque val Bool -> EvaluationResult Bool
        idAssumeCheckBoolPlc val =
            case asConstant val of
                Right (Some (ValueOf DefaultUniBool b)) -> EvaluationSuccess b
                _                                       -> EvaluationFailure

Here in the denotation we unlift the given value as a constant, check that its type tag is
'DefaultUniBool' and return the unlifted 'Bool'. If any of that fails, we return an explicit
'EvaluationFailure'.

This achieves almost the same as 'IdBool', which keeps all the bookkeeping behind the scenes, but
there is a minor difference: in case of error its message is ignored. It would be easy to allow for
returning an unlifting error from a builtin explicitly, but we don't need that for anything, hence
it's not implemented.

We call this style of manually calling 'asConstant' and matching on the type tag "manual unlifting".
As opposed to "automatic unlifting" that we were using before where 'Bool' in the type of the
denotation of a builtin causes the builtins machinery to convert the given argument to a 'Bool'
constant automatically behind the scenes.

3. There's a middle ground between automatic and manual unlifting to 'Bool', one can unlift a value
automatically as a constant and then unlift the result manually to 'Bool' using the 'SomeConstant'
wrapper:

    newtype SomeConstant uni (rep :: GHC.Type) = SomeConstant
        { unSomeConstant :: Some (ValueOf uni)
        }

'SomeConstant' is similar to 'Opaque' in that it has a @rep@ representing a Plutus type.
The difference is that 'Opaque' is a wrapper around an arbitrary value and 'SomeConstant' is a
wrapper around a constant. 'SomeConstant' allows one to automatically unlift an argument of a
built-in function as a constant with all 'asConstant' business kept behind the scenes, for example:

    toBuiltinMeaning IdSomeConstantBool =
        makeBuiltinMeaning
            idSomeConstantBoolPlc
            <costingFunction>
      where
        idSomeConstantBoolPlc :: SomeConstant uni Bool -> EvaluationResult Bool
        idSomeConstantBoolPlc = \case
            SomeConstant (Some (ValueOf DefaultUniBool b)) -> EvaluationSuccess b
            _                                              -> EvaluationFailure

Note how we no longer call 'asConstant' manually, but still manually match on 'DefaultUniBool'.

So there's a whole range of how "low-level" one can choose to be when defining a built-in function.
However it's not always possible to use automatic unlifting, see next.

4. If we try to define the following built-in function:

    toBuiltinMeaning NullList =
        makeBuiltinMeaning
            (null :: [a] -> Bool)
            <costingFunction>

we'll get an error, saying that a polymorphic built-in type can't be applied to a type variable.
It's not impossible to make it work, see Note [Unlifting values of built-in types], but not in the
general case, plus it has to be very inefficient.

Instead we have to use 'SomeConstant' to automatically unlift the argument as a constant and then
check that the value inside of it is a list (by matching on the type tag):

    toBuiltinMeaning NullList =
        makeBuiltinMeaning
            nullPlc
            <costingFunction>
        where
          nullPlc :: SomeConstant uni [a] -> EvaluationResult Bool
          nullPlc (SomeConstant (Some (ValueOf uniListA xs))) = do
              DefaultUniList _ <- pure uniListA
              pure $ null xs

('EvaluationResult' has a 'MonadFail' instance allowing us to use the @<pat> <- pure <expr>@ idiom)

As before, we have to match on the type tag, because there's no relation between @rep@ from
@SomeConstant uni rep@ and the constant that the built-in function actually receives at runtime
(someone could generate Untyped Plutus Core directly and apply 'nullPlc' to an 'Integer' or
whatever). @rep@ is only for the Plutus type checker to look at, it doesn't influence evaluation
in any way.

Here's a similar built-in function:

    toBuiltinMeaning FstPair =
        makeBuiltinMeaning
            fstPlc
            <costingFunction>
        where
          fstPlc :: SomeConstant uni (a, b) -> EvaluationResult (Opaque val a)
          fstPlc (SomeConstant (Some (ValueOf uniPairAB xy))) = do
              DefaultUniPair uniA _ <- pure uniPairAB  -- [1]
              pure . fromValueOf uniA $ fst xy         -- [2]

In this definition we extract the first element of a pair by checking that the given constant is
indeed a pair [1] and lifting its first element into @val@ using the type tag for the first
element [2] (extracted from the type tag for the whole pair constant [1]).

Note that it's fine to mix automatic unlifting for polymorphism not related to built-in types and
manual unlifting for arguments having non-monomorphized polymorphic built-in types, for example:

    toBuiltinMeaning ChooseList =
        makeBuiltinMeaning
            choosePlc
            <costingFunction>
        where
          choosePlc :: SomeConstant uni [a] -> b -> b -> EvaluationResult b
          choosePlc (SomeConstant (Some (ValueOf uniListA xs))) a b = do
            DefaultUniList _ <- pure uniListA
            pure $ case xs of
                []    -> a
                _ : _ -> b

Here @a@ appears inside @[]@, which is a polymorphic built-in type, and so we have to use
'SomeConstant' and check that the given constant is indeed a list, while @b@ doesn't appear inside
of any built-in type and so we don't need to instantiate it to 'Opaque' manually, the elaboration
machinery will do it for us.

Our final example is this:

    toBuiltinMeaning MkCons =
        makeBuiltinMeaning
            consPlc
            <costingFunction>
        where
          consPlc
              :: SomeConstant uni a -> SomeConstant uni [a] -> EvaluationResult (Opaque val [a])
          consPlc
            (SomeConstant (Some (ValueOf uniA x)))
            (SomeConstant (Some (ValueOf uniListA xs))) = do
                DefaultUniList uniA' <- pure uniListA  -- [1]
                Just Refl <- pure $ uniA `geq` uniA'   -- [2]
                pure . fromValueOf uniListA $ x : xs   -- [3]

Here we prepend an element to a list [3] after checking that the second argument is indeed a
list [1] and that the type tag of the element being prepended equals the type tag for elements of
the list [2] (extracted from the type tag for the whole list constant [1]).
-}

{- Note [Builtins and Plutus type checking]
There's a direct correspondence between the Haskell type of the denotation of a builtin and the
Plutus type of the builtin:

1. elaboration turns a Haskell type variable into a concrete Haskell type representing a Plutus type
   variable, which later becomes demoted (in the regular @singletons@ sense via 'KnownSymbol' etc)
   to a regular Haskell value representing a Plutus type variable (as a part of the AST)
2. a builtin head (i.e. a completely uninstantiated built-in type such as @Bool@ and @[]@) is
   considered abstract by the Plutus type checker. All the type checker cares about is being able to
   get the (Plutus) kind of a builtin head and check two builtin heads for equality
3. Plutus type normalization tears partially or fully instantiated built-in types (such as
   @[Integer]@) apart and creates a Plutus type application for each Haskell type application
4. 'Emitter' and 'EvaluationResult' do not appear on the Plutus side, since the logging and failure
   effects are implicit in Plutus as was discussed above
5. 'Opaque' and 'SomeConstant' both carry a Haskell @rep@ type argument representing some Plutus
   type to be used for Plutus type checking

This last part means that one can attach any (legal) @rep@ to an 'Opaque' or 'SomeConstant' and
it'll be used by the Plutus type checker completely regardless of what the built-in function
actually does. Let's look at some examples.

1. The following built-in function unlifts to 'Bool' and lifts the result back:

    toBuiltinMeaning IdIntegerAsBool =
        makeBuiltinMeaning
            idIntegerAsBool
            <costingFunction>
      where
        idIntegerAsBool :: SomeConstant uni Integer -> EvaluationResult (SomeConstant uni Integer)
        idIntegerAsBool = \case
            con@(SomeConstant (Some (ValueOf DefaultUniBool _))) -> EvaluationSuccess con
            _                                                    -> EvaluationFailure

but on the Plutus side its type is

    integer -> integer

because the @rep@ that 'SomeConstant' carries is 'Integer' in both the cases (in the type of the
argument, as well as in the type of the result).

This means that for this built-in function the Plutus type checker will accept a program that fails
at runtime due to a type mismatch and will reject a program that runs successfully. Other built-in
functions also can fail, e.g. the type of @ifThenElse@ says that the builtin expects a @Bool@ and
feeding it something else will result in evaluation failure, but 'idIntegerAsBool' is different:
it's respecting its type signature is what causes a failure, not disrespecting it.

2. Another example of an unsafe built-in function is this one that checks whether an argument is a
constant or not:

    toBuiltinMeaning IsConstant =
        makeBuiltinMeaning
            isConstantPlc
            <costingFunction>
      where
        -- The type signature is just for clarity, it's not required.
        isConstantPlc :: Opaque val a -> Bool
        isConstantPlc = isRight . asConstant

Its type on the Plutus side is

    all a. a -> bool

By parametricity any inhabitant of this type has to be either bottom or a function ignoring its
argument, but @IsConstant@ actually uses the argument and so we break parametricity with this
built-in function.

3. Finally, we can have a Plutus version of @unsafeCoerce@:

    toBuiltinMeaning UnsafeCoerce =
        makeBuiltinMeaning
            unsafeCoercePlc
            <costingFunction>
      where
        -- The type signature is just for clarity, it's not required.
        unsafeCoercePlc :: Opaque val a -> Opaque val b
        unsafeCoercePlc = Opaque . unOpaque

Its type on the Plutus side is

    all a b. a -> b

and thus this built-in function allows for viewing any Plutus expression as having an arbitrary
type. Which is of course not nearly as bad as @unsafeCoerce@ in Haskell, because in Plutus a
blob of memory representing an @Integer@ is not going to be viewed as a @[Bool]@ and an attempt to
actually extract that @[Bool]@ will result in evaluation failure, but this built-in function is
still not a good citizen of the Plutus type system.

One could of course simply wrap Haskell's @unsafeCoerce@ as a built-in function in Plutus, but it
goes without saying that this is not supposed to be done.

So overall one needs to be very careful when defining built-in functions that have explicit
'Opaque' and 'SomeConstant' arguments. Expressiveness doesn't come for free.

Read Note [Pattern matching on built-in types] next.
-}

{- Note [Pattern matching on built-in types]
At the moment we really only support direct pattern matching on enumeration types: 'Void', 'Unit',
'Bool' etc. This is because the denotation of a builtin cannot construct general terms (as opposed
to constants), only juggle the ones that were provided as arguments without changing them.
So e.g. if we wanted to add the following data type:

    newtype AnInt = AnInt Int

as a built-in type, we wouldn't be able to add the following function as its pattern matcher:

    matchAnInt :: AnInt -> (Int -> r) -> r
    matchAnInt (AnInt i) f = f i

because currently we cannot express the @f i@ part using the builtins machinery as that would
require applying an arbitrary Plutus Core function in the denotation of a builtin, which would
allow us to return arbitrary terms from the builtin application machinery, which is something
that we originally had, but decided to abandon due to performance concerns.

But it's still possible to have @AnInt@ as a built-in type, it's just that instead of trying to
make its pattern matcher into a builtin we can have the following builtin:

    anIntToInt :: AnInt -> Int
    anIntToInt (AnInt i) = i

which fits perfectly well into the builtins machinery.

Although that becomes annoying for more complex data types. For tuples we need to provide two
projection functions ('fst' and 'snd') instead of a single pattern matcher, which is not too bad,
but to get pattern matching on lists we need a more complicated setup. For example we can have three
built-in functions: @null@, @head@ and @tail@, plus require `Bool` to be in the universe, so that we
can define an equivalent of

    matchList :: [a] -> r -> (a -> [a] -> r) -> r
    matchList xs z f = if null xs then z else f (head xs) (tail xs)

If a constructor stores more than one value, the corresponding projection function packs them
into a (possibly nested) pair, for example for

    data Data
        = Constr Integer [Data]
        | <...>

we have (pseudocode):

    unConstrData (Constr i ds) = (i, ds)

In order to get pattern matching over 'Data' we need a projection function per constructor as well
as with lists, but writing (where the @Data@ suffix indicates that a function is a builtin that
somehow corresponds to a constructor of 'Data')

    if isConstrData d
        then uncurry fConstr $ unConstrData d
        else if isMapData d
            then fMap $ unMapData d
            else if isListData d
                then fList $ unListData d
                else <...>

is tedious and inefficient and so instead we have a single @chooseData@ builtin that matches on
its @Data@ argument and chooses the appropriate branch (type instantiations and strictness concerns
are omitted for clarity):

     chooseData
        (uncurry fConstr $ unConstrData d)
        (fMap $ unMapData d)
        (fList $ unListData d)
        <...>
        d

which, for example, evaluates to @fMap es@ when @d@ is @Map es@

We decided to handle lists the same way by using @chooseList@ rather than @null@ for consistency.

On the bright side, this encoding of pattern matchers does work, so maybe it's indeed worth to
prioritize performance over convenience, especially given the fact that performance is of a concern
to every single end user while the inconvenience is only a concern for the compiler writers and
we don't add complex built-in types too often.

It is not however clear if we can't get more performance gains by defining matchers directly as
higher-order built-in functions compared to forbidding them. Particularly since if higher-order
built-in functions were allowed, we could define not only matches, but also folds and keep recursion
on the Haskell side for conversions from 'Data', which can potentially have a huge positive impact
on performance.

Read Note [Representable built-in functions over polymorphic built-in types] next.
-}

{- Note [Representable built-in functions over polymorphic built-in types]
In Note [Pattern matching on built-in types] we discussed how general higher-order polymorphic
built-in functions are troubling, but polymorphic built-in functions can be troubling even in
the first-order case. In a Plutus program we always pair constants of built-in types with their
tags from the universe, which means that in order to produce a constant embedded into a program
we need the tag of the type of that constant. We can't get that tag from a Plutus type -- those
are gone at runtime, so the only place we can get a type tag from during evaluation is some already
existing constant. I.e. the following built-in function is representable:

    tail : all a. [a] -> [a]

because for constructing the result we need a type tag for @[a]@, but we have a value of that type
as an argument and so we can extract the type tag from it. Same applies to

    swap : all a b. (a, b) -> (b, a)

since 'SomeConstantOf' always contains a type tag for each type that a polymorphic built-in type is
instantiated with and so constructing a type tag for @(b, a)@ given type tags for @a@ and @b@ is
unproblematic.

And so neither

    cons : all a. a -> [a] -> [a]

is troubling (even though that ones requires checking at runtime that the element to be prepended
is of the same type as the type of the elements of the list as it's impossible to enforce this kind
of type safety in Haskell over possibly untyped PLC).

However consider the following imaginary builtin:

    nil : all a. [a]

we can't represent it for two reasons:

1. we don't have any argument providing us a type tag for @a@ and hence we can't construct a type
   tag for @[a]@
2. it would be a very unsound builtin to have. We can only instantiate built-in types with other
   built-in types and so allowing @nil {some_non_built_in_type}@ would be a lie that couldn't reduce
   to anything since it's not even possible to represent a built-in list with non-built-in elements
   (even if there's zero of them)

"Wait, but wouldn't @cons {some_non_built_in_type}@ be a lie as well?" -- No! Since @cons@ does not
just construct a list filled with elements of a non-built-in type but also expects one as an
argument and providing such an argument is impossible, 'cause it's pretty much the same thing as
populating 'Void' -- both values are equally unrepresentable. And so @cons {some_non_built_in_type}@
is a way to say @absurd@, which is perfectly fine to have.

Finally,

    comma :: all a b. a -> b -> (a, b)

is representable (because we can require arguments to be constants carrying universes with them,
which we can use to construct the resulting universe), but is still a lie, because instantiating
that builtin with non-built-in types is possible and so the PLC type checker won't throw on such
an instantiation, which will become 'EvalutionFailure' at runtime the moment unlifting of a
non-constant is attempted when a constant is expected.

So could we still get @nil@ or a safe version of @comma@ somehow? Well, we could have this
weirdness:

    nilOfTypeOf : all a. [a] -> [a]

i.e. ask for an already existing list, but ignore the actual list and only use the type tag.

But since we're ignoring the actual list, can't we just not pass it in the first place? And instead
pass around our good old friends, singletons. We should be able to do that, but it hasn't been
investigated. Perhaps something along the lines of adding the following constructor to 'DefaultUni':

    DefaultUniProtoSing :: DefaultUni (Esc (Proxy @GHC.Type))

and then defining

    nil : all a. sing a -> [a]

and then the Plutus Tx compiler can provide a type class or something for constructing singletons
for built-in types.

This was investigated in https://github.com/input-output-hk/plutus/pull/4337 but we decided not to
do it quite yet, even though it worked (the Plutus Tx part wasn't implemented).
-}

instance uni ~ DefaultUni => ToBuiltinMeaning uni DefaultFun where
    type CostingPart uni DefaultFun = BuiltinCostModel

    data BuiltinVersion DefaultFun = DefaultFunV1 | DefaultFunV2
        deriving stock (Enum, Bounded, Show)

    -- Integers
    toBuiltinMeaning
        :: forall val. HasMeaningIn uni val
        => BuiltinVersion DefaultFun -> DefaultFun -> BuiltinMeaning val BuiltinCostModel
    toBuiltinMeaning _ver AddInteger =
        makeBuiltinMeaning
            ((+) @Integer)
            (runCostingFunTwoArguments . paramAddInteger)
    toBuiltinMeaning _ver SubtractInteger =
        makeBuiltinMeaning
            ((-) @Integer)
            (runCostingFunTwoArguments . paramSubtractInteger)
    toBuiltinMeaning _ver MultiplyInteger =
        makeBuiltinMeaning
            ((*) @Integer)
            (runCostingFunTwoArguments . paramMultiplyInteger)
    toBuiltinMeaning _ver DivideInteger =
        makeBuiltinMeaning
            (nonZeroArg div)
            (runCostingFunTwoArguments . paramDivideInteger)
    toBuiltinMeaning _ver QuotientInteger =
        makeBuiltinMeaning
            (nonZeroArg quot)
            (runCostingFunTwoArguments . paramQuotientInteger)
    toBuiltinMeaning _ver RemainderInteger =
        makeBuiltinMeaning
            (nonZeroArg rem)
            (runCostingFunTwoArguments . paramRemainderInteger)
    toBuiltinMeaning _ver ModInteger =
        makeBuiltinMeaning
            (nonZeroArg mod)
            (runCostingFunTwoArguments . paramModInteger)
    toBuiltinMeaning _ver EqualsInteger =
        makeBuiltinMeaning
            ((==) @Integer)
            (runCostingFunTwoArguments . paramEqualsInteger)
    toBuiltinMeaning _ver LessThanInteger =
        makeBuiltinMeaning
            ((<) @Integer)
            (runCostingFunTwoArguments . paramLessThanInteger)
    toBuiltinMeaning _ver LessThanEqualsInteger =
        makeBuiltinMeaning
            ((<=) @Integer)
            (runCostingFunTwoArguments . paramLessThanEqualsInteger)
    -- Bytestrings
    toBuiltinMeaning _ver AppendByteString =
        makeBuiltinMeaning
            BS.append
            (runCostingFunTwoArguments . paramAppendByteString)
    toBuiltinMeaning ver ConsByteString =
        -- The costing function is the same for all versions of this builtin, but since the
        -- denotation of the builtin accepts constants of different types ('Integer' vs 'Word8'),
        -- the costing function needs to by polymorphic over the type of constant.
        let costingFun
                :: ExMemoryUsage a => BuiltinCostModel -> a -> BS.ByteString -> ExBudgetStream
            costingFun = runCostingFunTwoArguments . paramConsByteString
        -- See Note [Versioned builtins]
        in case ver of
            DefaultFunV1 -> makeBuiltinMeaning
               @(Integer -> BS.ByteString -> BS.ByteString)
               (\n xs -> BS.cons (fromIntegral @Integer n) xs)
               costingFun
            -- For versions other (i.e. larger) than V1, the first input must be in range [0..255].
            -- See Note [How to add a built-in function: simple cases]
            _ -> makeBuiltinMeaning
              @(Word8 -> BS.ByteString -> BS.ByteString)
              BS.cons
              costingFun
    toBuiltinMeaning _ver SliceByteString =
        makeBuiltinMeaning
            (\start n xs -> BS.take n (BS.drop start xs))
            (runCostingFunThreeArguments . paramSliceByteString)
    toBuiltinMeaning _ver LengthOfByteString =
        makeBuiltinMeaning
            BS.length
            (runCostingFunOneArgument . paramLengthOfByteString)
    toBuiltinMeaning _ver IndexByteString =
        makeBuiltinMeaning
            (\xs n -> if n >= 0 && n < BS.length xs then EvaluationSuccess $ toInteger $ BS.index xs n else EvaluationFailure)
            -- TODO: fix the mess above with `indexMaybe` from `bytestring >= 0.11.0.0`.
            (runCostingFunTwoArguments . paramIndexByteString)
    toBuiltinMeaning _ver EqualsByteString =
        makeBuiltinMeaning
            ((==) @BS.ByteString)
            (runCostingFunTwoArguments . paramEqualsByteString)
    toBuiltinMeaning _ver LessThanByteString =
        makeBuiltinMeaning
            ((<) @BS.ByteString)
            (runCostingFunTwoArguments . paramLessThanByteString)
    toBuiltinMeaning _ver LessThanEqualsByteString =
        makeBuiltinMeaning
            ((<=) @BS.ByteString)
            (runCostingFunTwoArguments . paramLessThanEqualsByteString)
    -- Cryptography and hashes
    toBuiltinMeaning _ver Sha2_256 =
        makeBuiltinMeaning
            Hash.sha2_256
            (runCostingFunOneArgument . paramSha2_256)
    toBuiltinMeaning _ver Sha3_256 =
        makeBuiltinMeaning
            Hash.sha3_256
            (runCostingFunOneArgument . paramSha3_256)
    toBuiltinMeaning _ver Blake2b_256 =
        makeBuiltinMeaning
            Hash.blake2b_256
            (runCostingFunOneArgument . paramBlake2b_256)
    toBuiltinMeaning ver VerifyEd25519Signature =
        let verifyEd25519Signature =
                case ver of
                  DefaultFunV1 -> verifyEd25519Signature_V1
                  _            -> verifyEd25519Signature_V2
        in makeBuiltinMeaning
           verifyEd25519Signature
           -- Benchmarks indicate that the two versions have very similar
           -- execution times, so it's safe to use the same costing function for
           -- both.
           (runCostingFunThreeArguments . paramVerifyEd25519Signature)
    {- Note [ECDSA secp256k1 signature verification].  An ECDSA signature
       consists of a pair of values (r,s), and for each value of r there are in
       fact two valid values of s, one effectively the negative of the other.
       The Bitcoin implementation that underlies `verifyEcdsaSecp256k1Signature`
       expects that the lower of the two possible values of the s component of
       the signature is used, returning `false` immediately if that's not the
       case.  It appears that this restriction is peculiar to Bitcoin, and ECDSA
       schemes in general don't require it.  Thus this function may be more
       restrictive than expected.  See

          https://github.com/bitcoin/bips/blob/master/bip-0146.mediawiki#LOW_S

       and the implementation of secp256k1_ecdsa_verify in

          https://github.com/bitcoin-core/secp256k1.
     -}
    toBuiltinMeaning _ver VerifyEcdsaSecp256k1Signature =
        makeBuiltinMeaning
            verifyEcdsaSecp256k1Signature
            (runCostingFunThreeArguments . paramVerifyEcdsaSecp256k1Signature)
    toBuiltinMeaning _ver VerifySchnorrSecp256k1Signature =
        makeBuiltinMeaning
            verifySchnorrSecp256k1Signature
            (runCostingFunThreeArguments . paramVerifySchnorrSecp256k1Signature)
    -- Strings
    toBuiltinMeaning _ver AppendString =
        makeBuiltinMeaning
            ((<>) @Text)
            (runCostingFunTwoArguments . paramAppendString)
    toBuiltinMeaning _ver EqualsString =
        makeBuiltinMeaning
            ((==) @Text)
            (runCostingFunTwoArguments . paramEqualsString)
    toBuiltinMeaning _ver EncodeUtf8 =
        makeBuiltinMeaning
            encodeUtf8
            (runCostingFunOneArgument . paramEncodeUtf8)
    toBuiltinMeaning _ver DecodeUtf8 =
        makeBuiltinMeaning
            (reoption @_ @EvaluationResult . decodeUtf8')
            (runCostingFunOneArgument . paramDecodeUtf8)
    -- Bool
    toBuiltinMeaning _ver IfThenElse =
        makeBuiltinMeaning
            (\b x y -> if b then x else y)
            (runCostingFunThreeArguments . paramIfThenElse)
    -- Unit
    toBuiltinMeaning _ver ChooseUnit =
        makeBuiltinMeaning
            (\() a -> a)
            (runCostingFunTwoArguments . paramChooseUnit)
    -- Tracing
    toBuiltinMeaning _ver Trace =
        makeBuiltinMeaning
            (\text a -> a <$ emit text)
            (runCostingFunTwoArguments . paramTrace)
    -- Pairs
    toBuiltinMeaning _ver FstPair =
        makeBuiltinMeaning
            fstPlc
            (runCostingFunOneArgument . paramFstPair)
        where
          fstPlc :: SomeConstant uni (a, b) -> EvaluationResult (Opaque val a)
          fstPlc (SomeConstant (Some (ValueOf uniPairAB xy))) = do
              DefaultUniPair uniA _ <- pure uniPairAB
              pure . fromValueOf uniA $ fst xy
          {-# INLINE fstPlc #-}
    toBuiltinMeaning _ver SndPair =
        makeBuiltinMeaning
            sndPlc
            (runCostingFunOneArgument . paramSndPair)
        where
          sndPlc :: SomeConstant uni (a, b) -> EvaluationResult (Opaque val b)
          sndPlc (SomeConstant (Some (ValueOf uniPairAB xy))) = do
              DefaultUniPair _ uniB <- pure uniPairAB
              pure . fromValueOf uniB $ snd xy
          {-# INLINE sndPlc #-}
    -- Lists
    toBuiltinMeaning _ver ChooseList =
        makeBuiltinMeaning
            choosePlc
            (runCostingFunThreeArguments . paramChooseList)
        where
          choosePlc :: SomeConstant uni [a] -> b -> b -> EvaluationResult b
          choosePlc (SomeConstant (Some (ValueOf uniListA xs))) a b = do
            DefaultUniList _ <- pure uniListA
            pure $ case xs of
                []    -> a
                _ : _ -> b
          {-# INLINE choosePlc #-}
    toBuiltinMeaning _ver MkCons =
        makeBuiltinMeaning
            consPlc
            (runCostingFunTwoArguments . paramMkCons)
        where
          consPlc
              :: SomeConstant uni a -> SomeConstant uni [a] -> EvaluationResult (Opaque val [a])
          consPlc
            (SomeConstant (Some (ValueOf uniA x)))
            (SomeConstant (Some (ValueOf uniListA xs))) = do
                DefaultUniList uniA' <- pure uniListA
                -- Checking that the type of the constant is the same as the type of the elements
                -- of the unlifted list. Note that there's no way we could enforce this statically
                -- since in UPLC one can create an ill-typed program that attempts to prepend
                -- a value of the wrong type to a list.
                -- Should that rather give us an 'UnliftingError'? For that we need
                -- https://github.com/input-output-hk/plutus/pull/3035
                Just Refl <- pure $ uniA `geq` uniA'
                pure . fromValueOf uniListA $ x : xs
          {-# INLINE consPlc #-}
    toBuiltinMeaning _ver HeadList =
        makeBuiltinMeaning
            headPlc
            (runCostingFunOneArgument . paramHeadList)
        where
          headPlc :: SomeConstant uni [a] -> EvaluationResult (Opaque val a)
          headPlc (SomeConstant (Some (ValueOf uniListA xs))) = do
              DefaultUniList uniA <- pure uniListA
              x : _ <- pure xs
              pure $ fromValueOf uniA x
          {-# INLINE headPlc #-}
    toBuiltinMeaning _ver TailList =
        makeBuiltinMeaning
            tailPlc
            (runCostingFunOneArgument . paramTailList)
        where
          tailPlc :: SomeConstant uni [a] -> EvaluationResult (Opaque val [a])
          tailPlc (SomeConstant (Some (ValueOf uniListA xs))) = do
              DefaultUniList _ <- pure uniListA
              _ : xs' <- pure xs
              pure $ fromValueOf uniListA xs'
          {-# INLINE tailPlc #-}
    toBuiltinMeaning _ver NullList =
        makeBuiltinMeaning
            nullPlc
            (runCostingFunOneArgument . paramNullList)
        where
          nullPlc :: SomeConstant uni [a] -> EvaluationResult Bool
          nullPlc (SomeConstant (Some (ValueOf uniListA xs))) = do
              DefaultUniList _ <- pure uniListA
              pure $ null xs
          {-# INLINE nullPlc #-}

    -- Data
    toBuiltinMeaning _ver ChooseData =
        makeBuiltinMeaning
            (\d
              xConstr
              xMap xList xI xB ->
                  case d of
                    Constr {} -> xConstr
                    Map    {} -> xMap
                    List   {} -> xList
                    I      {} -> xI
                    B      {} -> xB)
            (runCostingFunSixArguments . paramChooseData)
    toBuiltinMeaning _ver ConstrData =
        makeBuiltinMeaning
            Constr
            (runCostingFunTwoArguments . paramConstrData)
    toBuiltinMeaning _ver MapData =
        makeBuiltinMeaning
            Map
            (runCostingFunOneArgument . paramMapData)
    toBuiltinMeaning _ver ListData =
        makeBuiltinMeaning
            List
            (runCostingFunOneArgument . paramListData)
    toBuiltinMeaning _ver IData =
        makeBuiltinMeaning
            I
            (runCostingFunOneArgument . paramIData)
    toBuiltinMeaning _ver BData =
        makeBuiltinMeaning
            B
            (runCostingFunOneArgument . paramBData)
    toBuiltinMeaning _ver UnConstrData =
        makeBuiltinMeaning
            (\case
                Constr i ds -> EvaluationSuccess (i, ds)
                _           -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnConstrData)
    toBuiltinMeaning _ver UnMapData =
        makeBuiltinMeaning
            (\case
                Map es -> EvaluationSuccess es
                _      -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnMapData)
    toBuiltinMeaning _ver UnListData =
        makeBuiltinMeaning
            (\case
                List ds -> EvaluationSuccess ds
                _       -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnListData)
    toBuiltinMeaning _ver UnIData =
        makeBuiltinMeaning
            (\case
                I i -> EvaluationSuccess i
                _   -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnIData)
    toBuiltinMeaning _ver UnBData =
        makeBuiltinMeaning
            (\case
                B b -> EvaluationSuccess b
                _   -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnBData)
    toBuiltinMeaning _ver EqualsData =
        makeBuiltinMeaning
            ((==) @Data)
            (runCostingFunTwoArguments . paramEqualsData)
    toBuiltinMeaning _ver SerialiseData =
        makeBuiltinMeaning
            (BSL.toStrict . serialise @Data)
            (runCostingFunOneArgument . paramSerialiseData)
    -- Misc constructors
    toBuiltinMeaning _ver MkPairData =
        makeBuiltinMeaning
            ((,) @Data @Data)
            (runCostingFunTwoArguments . paramMkPairData)
    toBuiltinMeaning _ver MkNilData =
        -- Nullary built-in functions don't work, so we need a unit argument.
        -- We don't really need this built-in function, see Note [Constants vs built-in functions],
        -- but we keep it around for historical reasons and convenience.
        makeBuiltinMeaning
            (\() -> [] @Data)
            (runCostingFunOneArgument . paramMkNilData)
    toBuiltinMeaning _ver MkNilPairData =
        -- Nullary built-in functions don't work, so we need a unit argument.
        -- We don't really need this built-in function, see Note [Constants vs built-in functions],
        -- but we keep it around for historical reasons and convenience.
        makeBuiltinMeaning
            (\() -> [] @(Data,Data))
            (runCostingFunOneArgument . paramMkNilPairData)
    -- BLS12_381.G1
    toBuiltinMeaning _var Bls12_381_G1_add =
        makeBuiltinMeaning
            BLS12_381.G1.add
            (runCostingFunTwoArguments . paramBls12_381_G1_add)
    toBuiltinMeaning _var Bls12_381_G1_neg =
        makeBuiltinMeaning
            BLS12_381.G1.neg
            (runCostingFunOneArgument . paramBls12_381_G1_neg)
    toBuiltinMeaning _var Bls12_381_G1_scalarMul =
        makeBuiltinMeaning
            BLS12_381.G1.scalarMul
            (runCostingFunTwoArguments . paramBls12_381_G1_scalarMul)
    toBuiltinMeaning _var Bls12_381_G1_compress =
        makeBuiltinMeaning
            BLS12_381.G1.compress
            (runCostingFunOneArgument . paramBls12_381_G1_compress)
    toBuiltinMeaning _var Bls12_381_G1_uncompress =
        makeBuiltinMeaning
            uncompressG1
            (runCostingFunOneArgument . paramBls12_381_G1_uncompress)
        where uncompressG1 s =
                  case BLS12_381.G1.uncompress s of
                    Left _  -> EvaluationFailure
                    Right p -> EvaluationSuccess p
    toBuiltinMeaning _var Bls12_381_G1_hashToGroup =
        makeBuiltinMeaning
            BLS12_381.G1.hashToGroup
            (runCostingFunOneArgument . paramBls12_381_G1_hashToGroup)
    toBuiltinMeaning _var Bls12_381_G1_equal =
        makeBuiltinMeaning
            ((==) @BLS12_381.G1.Element)
            (runCostingFunTwoArguments . paramBls12_381_G1_equal)
    -- BLS12_381.G2
    toBuiltinMeaning _var Bls12_381_G2_add =
        makeBuiltinMeaning
            BLS12_381.G2.add
            (runCostingFunTwoArguments . paramBls12_381_G2_add)
    toBuiltinMeaning _var Bls12_381_G2_neg =
        makeBuiltinMeaning
            BLS12_381.G2.neg
            (runCostingFunOneArgument . paramBls12_381_G2_neg)
    toBuiltinMeaning _var Bls12_381_G2_scalarMul =
        makeBuiltinMeaning
            BLS12_381.G2.scalarMul
            (runCostingFunTwoArguments . paramBls12_381_G2_scalarMul)
    toBuiltinMeaning _var Bls12_381_G2_compress =
        makeBuiltinMeaning
            BLS12_381.G2.compress
            (runCostingFunOneArgument . paramBls12_381_G2_compress)
    toBuiltinMeaning _var Bls12_381_G2_uncompress =
        makeBuiltinMeaning
            uncompressG2
            (runCostingFunOneArgument . paramBls12_381_G2_uncompress)
        where uncompressG2 s =
                  case BLS12_381.G2.uncompress s of
                    Left _  -> EvaluationFailure
                    Right p -> EvaluationSuccess p
    toBuiltinMeaning _var Bls12_381_G2_hashToGroup =
        makeBuiltinMeaning
            BLS12_381.G2.hashToGroup
            (runCostingFunOneArgument . paramBls12_381_G2_hashToGroup)
    toBuiltinMeaning _var Bls12_381_G2_equal =
        makeBuiltinMeaning
            ((==) @BLS12_381.G2.Element)
            (runCostingFunTwoArguments . paramBls12_381_G2_equal)
    -- BLS12_381.Pairing
    toBuiltinMeaning _var Bls12_381_millerLoop =
        makeBuiltinMeaning
            BLS12_381.Pairing.millerLoop
            (runCostingFunTwoArguments . paramBls12_381_millerLoop)
    toBuiltinMeaning _var Bls12_381_mulMlResult =
        makeBuiltinMeaning
            BLS12_381.Pairing.mulMlResult
            (runCostingFunTwoArguments . paramBls12_381_mulMlResult)
    toBuiltinMeaning _var Bls12_381_finalVerify =
        makeBuiltinMeaning
            BLS12_381.Pairing.finalVerify
            (runCostingFunTwoArguments . paramBls12_381_finalVerify)
    -- See Note [Inlining meanings of builtins].
    {-# INLINE toBuiltinMeaning #-}

instance Default (BuiltinVersion DefaultFun) where
    def = DefaultFunV2

instance Pretty (BuiltinVersion DefaultFun) where
    pretty = viaShow

-- It's set deliberately to give us "extra room" in the binary format to add things without running
-- out of space for tags (expanding the space would change the binary format for people who're
-- implementing it manually). So we have to set it manually.
-- | Using 7 bits to encode builtin tags.
builtinTagWidth :: NumBits
builtinTagWidth = 7

encodeBuiltin :: Word8 -> Flat.Encoding
encodeBuiltin = eBits builtinTagWidth

decodeBuiltin :: Get Word8
decodeBuiltin = dBEBits8 builtinTagWidth

-- See Note [Stable encoding of PLC]
instance Flat DefaultFun where
    encode = encodeBuiltin . \case
              AddInteger                      -> 0
              SubtractInteger                 -> 1
              MultiplyInteger                 -> 2
              DivideInteger                   -> 3
              QuotientInteger                 -> 4
              RemainderInteger                -> 5
              ModInteger                      -> 6
              EqualsInteger                   -> 7
              LessThanInteger                 -> 8
              LessThanEqualsInteger           -> 9

              AppendByteString                -> 10
              ConsByteString                  -> 11
              SliceByteString                 -> 12
              LengthOfByteString              -> 13
              IndexByteString                 -> 14
              EqualsByteString                -> 15
              LessThanByteString              -> 16
              LessThanEqualsByteString        -> 17

              Sha2_256                        -> 18
              Sha3_256                        -> 19
              Blake2b_256                     -> 20
              VerifyEd25519Signature          -> 21

              AppendString                    -> 22
              EqualsString                    -> 23
              EncodeUtf8                      -> 24
              DecodeUtf8                      -> 25

              IfThenElse                      -> 26

              ChooseUnit                      -> 27

              Trace                           -> 28

              FstPair                         -> 29
              SndPair                         -> 30

              ChooseList                      -> 31
              MkCons                          -> 32
              HeadList                        -> 33
              TailList                        -> 34
              NullList                        -> 35

              ChooseData                      -> 36
              ConstrData                      -> 37
              MapData                         -> 38
              ListData                        -> 39
              IData                           -> 40
              BData                           -> 41
              UnConstrData                    -> 42
              UnMapData                       -> 43
              UnListData                      -> 44
              UnIData                         -> 45
              UnBData                         -> 46
              EqualsData                      -> 47
              MkPairData                      -> 48
              MkNilData                       -> 49
              MkNilPairData                   -> 50
              SerialiseData                   -> 51
              VerifyEcdsaSecp256k1Signature   -> 52
              VerifySchnorrSecp256k1Signature -> 53
              Bls12_381_G1_add                -> 54
              Bls12_381_G1_neg                -> 55
              Bls12_381_G1_scalarMul          -> 56
              Bls12_381_G1_equal              -> 57
              Bls12_381_G1_compress           -> 58
              Bls12_381_G1_uncompress         -> 59
              Bls12_381_G1_hashToGroup        -> 60
              Bls12_381_G2_add                -> 61
              Bls12_381_G2_neg                -> 62
              Bls12_381_G2_scalarMul          -> 63
              Bls12_381_G2_equal              -> 64
              Bls12_381_G2_compress           -> 65
              Bls12_381_G2_uncompress         -> 66
              Bls12_381_G2_hashToGroup        -> 67
              Bls12_381_millerLoop            -> 68
              Bls12_381_mulMlResult           -> 69
              Bls12_381_finalVerify           -> 70

    decode = go =<< decodeBuiltin
        where go 0  = pure AddInteger
              go 1  = pure SubtractInteger
              go 2  = pure MultiplyInteger
              go 3  = pure DivideInteger
              go 4  = pure QuotientInteger
              go 5  = pure RemainderInteger
              go 6  = pure ModInteger
              go 7  = pure EqualsInteger
              go 8  = pure LessThanInteger
              go 9  = pure LessThanEqualsInteger
              go 10 = pure AppendByteString
              go 11 = pure ConsByteString
              go 12 = pure SliceByteString
              go 13 = pure LengthOfByteString
              go 14 = pure IndexByteString
              go 15 = pure EqualsByteString
              go 16 = pure LessThanByteString
              go 17 = pure LessThanEqualsByteString
              go 18 = pure Sha2_256
              go 19 = pure Sha3_256
              go 20 = pure Blake2b_256
              go 21 = pure VerifyEd25519Signature
              go 22 = pure AppendString
              go 23 = pure EqualsString
              go 24 = pure EncodeUtf8
              go 25 = pure DecodeUtf8
              go 26 = pure IfThenElse
              go 27 = pure ChooseUnit
              go 28 = pure Trace
              go 29 = pure FstPair
              go 30 = pure SndPair
              go 31 = pure ChooseList
              go 32 = pure MkCons
              go 33 = pure HeadList
              go 34 = pure TailList
              go 35 = pure NullList
              go 36 = pure ChooseData
              go 37 = pure ConstrData
              go 38 = pure MapData
              go 39 = pure ListData
              go 40 = pure IData
              go 41 = pure BData
              go 42 = pure UnConstrData
              go 43 = pure UnMapData
              go 44 = pure UnListData
              go 45 = pure UnIData
              go 46 = pure UnBData
              go 47 = pure EqualsData
              go 48 = pure MkPairData
              go 49 = pure MkNilData
              go 50 = pure MkNilPairData
              go 51 = pure SerialiseData
              go 52 = pure VerifyEcdsaSecp256k1Signature
              go 53 = pure VerifySchnorrSecp256k1Signature
              go 54 = pure Bls12_381_G1_add
              go 55 = pure Bls12_381_G1_neg
              go 56 = pure Bls12_381_G1_scalarMul
              go 57 = pure Bls12_381_G1_equal
              go 58 = pure Bls12_381_G1_compress
              go 59 = pure Bls12_381_G1_uncompress
              go 60 = pure Bls12_381_G1_hashToGroup
              go 61 = pure Bls12_381_G2_add
              go 62 = pure Bls12_381_G2_neg
              go 63 = pure Bls12_381_G2_scalarMul
              go 64 = pure Bls12_381_G2_equal
              go 65 = pure Bls12_381_G2_compress
              go 66 = pure Bls12_381_G2_uncompress
              go 67 = pure Bls12_381_G2_hashToGroup
              go 68 = pure Bls12_381_millerLoop
              go 69 = pure Bls12_381_mulMlResult
              go 70 = pure Bls12_381_finalVerify
              go t  = fail $ "Failed to decode builtin tag, got: " ++ show t

    size _ n = n + builtinTagWidth
