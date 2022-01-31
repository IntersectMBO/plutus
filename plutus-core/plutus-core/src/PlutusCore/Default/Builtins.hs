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
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty

import Crypto (verifySECP256k1Signature, verifySignature)
import Data.ByteString qualified as BS
import Data.ByteString.Hash qualified as Hash
import Data.Char
import Data.Ix
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8', encodeUtf8)
import Flat hiding (from, to)
import Flat.Decoder
import Flat.Encoder as Flat

-- See Note [Pattern matching on built-in types].
-- TODO: should we have the commonest builtins at the front to have more compact encoding?
-- | Default built-in functions.
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
    | VerifySignature
    | VerifySECP256k1Signature
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
    -- Misc constructors
    -- Constructors that we need for constructing e.g. Data. Polymorphic builtin
    -- constructors are often problematic (See note [Representable built-in
    -- functions over polymorphic built-in types])
    | MkPairData
    | MkNilData
    | MkNilPairData
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Hashable, Ix, PrettyBy PrettyConfigPlc)

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
    memoryUsage _ = 1

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

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
            (\text a -> a <$ emitM text)
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
(for the purpose of this explanation it doesn't matter what @VarN@ actually is).
See Note [Implementation of polymorphic built-in functions] for what 'Opaque' is.

So the type from the above elaborates to

    Bool -> Opaque val Var0 -> Opaque val Var0 -> Opaque val Var0

We could've specified this type explicitly (leaving out the @Var0@ thing for the elaboration
machinery to figure out):

    toBuiltinMeaning IfThenElse =
        makeBuiltinMeaning
            @(Bool -> Opaque val _ -> Opaque val _ -> Opaque val _)
            (\b x y -> if b then x else y)
            <costingFunction>

and this would be equivalent to the original definition. We didn't do that, because why bother if
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
            (\text a -> a <$ emitM text)
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
-}

instance uni ~ DefaultUni => ToBuiltinMeaning uni DefaultFun where
    type CostingPart uni DefaultFun = BuiltinCostModel
    -- Integers
    toBuiltinMeaning
        :: forall val. HasConstantIn uni val
        => DefaultFun -> BuiltinMeaning val BuiltinCostModel
    toBuiltinMeaning AddInteger =
        makeBuiltinMeaning
            ((+) @Integer)
            (runCostingFunTwoArguments . paramAddInteger)
    toBuiltinMeaning SubtractInteger =
        makeBuiltinMeaning
            ((-) @Integer)
            (runCostingFunTwoArguments . paramSubtractInteger)
    toBuiltinMeaning MultiplyInteger =
        makeBuiltinMeaning
            ((*) @Integer)
            (runCostingFunTwoArguments . paramMultiplyInteger)
    toBuiltinMeaning DivideInteger =
        makeBuiltinMeaning
            (nonZeroArg div)
            (runCostingFunTwoArguments . paramDivideInteger)
    toBuiltinMeaning QuotientInteger =
        makeBuiltinMeaning
            (nonZeroArg quot)
            (runCostingFunTwoArguments . paramQuotientInteger)
    toBuiltinMeaning RemainderInteger =
        makeBuiltinMeaning
            (nonZeroArg rem)
            (runCostingFunTwoArguments . paramRemainderInteger)
    toBuiltinMeaning ModInteger =
        makeBuiltinMeaning
            (nonZeroArg mod)
            (runCostingFunTwoArguments . paramModInteger)
    toBuiltinMeaning EqualsInteger =
        makeBuiltinMeaning
            ((==) @Integer)
            (runCostingFunTwoArguments . paramEqualsInteger)
    toBuiltinMeaning LessThanInteger =
        makeBuiltinMeaning
            ((<) @Integer)
            (runCostingFunTwoArguments . paramLessThanInteger)
    toBuiltinMeaning LessThanEqualsInteger =
        makeBuiltinMeaning
            ((<=) @Integer)
            (runCostingFunTwoArguments . paramLessThanEqualsInteger)
    -- Bytestrings
    toBuiltinMeaning AppendByteString =
        makeBuiltinMeaning
            BS.append
            (runCostingFunTwoArguments . paramAppendByteString)
    toBuiltinMeaning ConsByteString =
        makeBuiltinMeaning
            (\n xs -> BS.cons (fromIntegral @Integer n) xs)
            (runCostingFunTwoArguments . paramConsByteString)
    toBuiltinMeaning SliceByteString =
        makeBuiltinMeaning
            (\start n xs -> BS.take n (BS.drop start xs))
            (runCostingFunThreeArguments . paramSliceByteString)
    toBuiltinMeaning LengthOfByteString =
        makeBuiltinMeaning
            BS.length
            (runCostingFunOneArgument . paramLengthOfByteString)
    toBuiltinMeaning IndexByteString =
        makeBuiltinMeaning
            (\xs n -> if n >= 0 && n < BS.length xs then EvaluationSuccess $ toInteger $ BS.index xs n else EvaluationFailure)
            -- TODO: fix the mess above with `indexMaybe` from `bytestring >= 0.11.0.0`.
            (runCostingFunTwoArguments . paramIndexByteString)
    toBuiltinMeaning EqualsByteString =
        makeBuiltinMeaning
            ((==) @BS.ByteString)
            (runCostingFunTwoArguments . paramEqualsByteString)
    toBuiltinMeaning LessThanByteString =
        makeBuiltinMeaning
            ((<) @BS.ByteString)
            (runCostingFunTwoArguments . paramLessThanByteString)
    toBuiltinMeaning LessThanEqualsByteString =
        makeBuiltinMeaning
            ((<=) @BS.ByteString)
            (runCostingFunTwoArguments . paramLessThanEqualsByteString)
    -- Cryptography and hashes
    toBuiltinMeaning Sha2_256 =
        makeBuiltinMeaning
            Hash.sha2
            (runCostingFunOneArgument . paramSha2_256)
    toBuiltinMeaning Sha3_256 =
        makeBuiltinMeaning
            Hash.sha3
            (runCostingFunOneArgument . paramSha3_256)
    toBuiltinMeaning Blake2b_256 =
        makeBuiltinMeaning
            Hash.blake2b
            (runCostingFunOneArgument . paramBlake2b)
    toBuiltinMeaning VerifySignature =
        makeBuiltinMeaning
            (verifySignature @EvaluationResult)
            (runCostingFunThreeArguments . paramVerifySignature)
    toBuiltinMeaning VerifySECP256k1Signature =
        makeBuiltinMeaning
            verifySECP256k1Signature
            mempty
    -- Strings
    toBuiltinMeaning AppendString =
        makeBuiltinMeaning
            ((<>) @Text)
            (runCostingFunTwoArguments . paramAppendString)
    toBuiltinMeaning EqualsString =
        makeBuiltinMeaning
            ((==) @Text)
            (runCostingFunTwoArguments . paramEqualsString)
    toBuiltinMeaning EncodeUtf8 =
        makeBuiltinMeaning
            encodeUtf8
            (runCostingFunOneArgument . paramEncodeUtf8)
    toBuiltinMeaning DecodeUtf8 =
        makeBuiltinMeaning
            (reoption @_ @EvaluationResult . decodeUtf8')
            (runCostingFunOneArgument . paramDecodeUtf8)
    -- Bool
    toBuiltinMeaning IfThenElse =
        makeBuiltinMeaning
            (\b x y -> if b then x else y)
            (runCostingFunThreeArguments . paramIfThenElse)
    -- Unit
    toBuiltinMeaning ChooseUnit =
        makeBuiltinMeaning
            (\() a -> a)
            (runCostingFunTwoArguments . paramChooseUnit)
    -- Tracing
    toBuiltinMeaning Trace =
        makeBuiltinMeaning
            (\text a -> a <$ emitM text)
            (runCostingFunTwoArguments . paramTrace)
    -- Pairs
    toBuiltinMeaning FstPair =
        makeBuiltinMeaning
            fstPlc
            (runCostingFunOneArgument . paramFstPair)
        where
          fstPlc :: SomeConstant uni (a, b) -> EvaluationResult (Opaque val a)
          fstPlc (SomeConstant (Some (ValueOf uniPairAB xy))) = do
              DefaultUniPair uniA _ <- pure uniPairAB
              pure . fromConstant . someValueOf uniA $ fst xy
          {-# INLINE fstPlc #-}
    toBuiltinMeaning SndPair =
        makeBuiltinMeaning
            sndPlc
            (runCostingFunOneArgument . paramSndPair)
        where
          sndPlc :: SomeConstant uni (a, b) -> EvaluationResult (Opaque val b)
          sndPlc (SomeConstant (Some (ValueOf uniPairAB xy))) = do
              DefaultUniPair _ uniB <- pure uniPairAB
              pure . fromConstant . someValueOf uniB $ snd xy
          {-# INLINE sndPlc #-}
    -- Lists
    toBuiltinMeaning ChooseList =
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
    toBuiltinMeaning MkCons =
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
                pure . fromConstant . someValueOf uniListA $ x : xs
          {-# INLINE consPlc #-}
    toBuiltinMeaning HeadList =
        makeBuiltinMeaning
            headPlc
            (runCostingFunOneArgument . paramHeadList)
        where
          headPlc :: SomeConstant uni [a] -> EvaluationResult (Opaque val a)
          headPlc (SomeConstant (Some (ValueOf uniListA xs))) = do
              DefaultUniList uniA <- pure uniListA
              x : _ <- pure xs
              pure . fromConstant $ someValueOf uniA x
          {-# INLINE headPlc #-}
    toBuiltinMeaning TailList =
        makeBuiltinMeaning
            tailPlc
            (runCostingFunOneArgument . paramTailList)
        where
          tailPlc :: SomeConstant uni [a] -> EvaluationResult (Opaque val [a])
          tailPlc (SomeConstant (Some (ValueOf uniListA xs))) = do
              DefaultUniList _ <- pure uniListA
              _ : xs' <- pure xs
              pure . fromConstant $ someValueOf uniListA xs'
          {-# INLINE tailPlc #-}
    toBuiltinMeaning NullList =
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
    toBuiltinMeaning ChooseData =
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
    toBuiltinMeaning ConstrData =
        makeBuiltinMeaning
            Constr
            (runCostingFunTwoArguments . paramConstrData)
    toBuiltinMeaning MapData =
        makeBuiltinMeaning
            Map
            (runCostingFunOneArgument . paramMapData)
    toBuiltinMeaning ListData =
        makeBuiltinMeaning
            List
            (runCostingFunOneArgument . paramListData)
    toBuiltinMeaning IData =
        makeBuiltinMeaning
            I
            (runCostingFunOneArgument . paramIData)
    toBuiltinMeaning BData =
        makeBuiltinMeaning
            B
            (runCostingFunOneArgument . paramBData)
    toBuiltinMeaning UnConstrData =
        makeBuiltinMeaning
            (\case
                Constr i ds -> EvaluationSuccess (i, ds)
                _           -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnConstrData)
    toBuiltinMeaning UnMapData =
        makeBuiltinMeaning
            (\case
                Map es -> EvaluationSuccess es
                _      -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnMapData)
    toBuiltinMeaning UnListData =
        makeBuiltinMeaning
            (\case
                List ds -> EvaluationSuccess ds
                _       -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnListData)
    toBuiltinMeaning UnIData =
        makeBuiltinMeaning
            (\case
                I i -> EvaluationSuccess i
                _   -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnIData)
    toBuiltinMeaning UnBData =
        makeBuiltinMeaning
            (\case
                B b -> EvaluationSuccess b
                _   -> EvaluationFailure)
            (runCostingFunOneArgument . paramUnBData)
    toBuiltinMeaning EqualsData =
        makeBuiltinMeaning
            ((==) @Data)
            (runCostingFunTwoArguments . paramEqualsData)
    -- Misc constructors
    toBuiltinMeaning MkPairData =
        makeBuiltinMeaning
            ((,) @Data @Data)
            (runCostingFunTwoArguments . paramMkPairData)
    toBuiltinMeaning MkNilData =
        -- Nullary builtins don't work, so we need a unit argument
        makeBuiltinMeaning
            (\() -> [] @Data)
            (runCostingFunOneArgument . paramMkNilData)
    toBuiltinMeaning MkNilPairData =
        -- Nullary builtins don't work, so we need a unit argument
        makeBuiltinMeaning
            (\() -> [] @(Data,Data))
            (runCostingFunOneArgument . paramMkNilPairData)

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
              AddInteger               -> 0
              SubtractInteger          -> 1
              MultiplyInteger          -> 2
              DivideInteger            -> 3
              QuotientInteger          -> 4
              RemainderInteger         -> 5
              ModInteger               -> 6
              EqualsInteger            -> 7
              LessThanInteger          -> 8
              LessThanEqualsInteger    -> 9

              AppendByteString         -> 10
              ConsByteString           -> 11
              SliceByteString          -> 12
              LengthOfByteString       -> 13
              IndexByteString          -> 14
              EqualsByteString         -> 15
              LessThanByteString       -> 16
              LessThanEqualsByteString -> 17

              Sha2_256                 -> 18
              Sha3_256                 -> 19
              Blake2b_256              -> 20
              VerifySignature          -> 21
              VerifySECP256k1Signature -> 51

              AppendString             -> 22
              EqualsString             -> 23
              EncodeUtf8               -> 24
              DecodeUtf8               -> 25

              IfThenElse               -> 26

              ChooseUnit               -> 27

              Trace                    -> 28

              FstPair                  -> 29
              SndPair                  -> 30

              ChooseList               -> 31
              MkCons                   -> 32
              HeadList                 -> 33
              TailList                 -> 34
              NullList                 -> 35

              ChooseData               -> 36
              ConstrData               -> 37
              MapData                  -> 38
              ListData                 -> 39
              IData                    -> 40
              BData                    -> 41
              UnConstrData             -> 42
              UnMapData                -> 43
              UnListData               -> 44
              UnIData                  -> 45
              UnBData                  -> 46
              EqualsData               -> 47

              MkPairData               -> 48
              MkNilData                -> 49
              MkNilPairData            -> 50

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
              go 21 = pure VerifySignature
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
              go 51 = pure VerifySECP256k1Signature
              go t  = fail $ "Failed to decode builtin tag, got: " ++ show t

    size _ n = n + builtinTagWidth
