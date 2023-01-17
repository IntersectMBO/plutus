-- editorconfig-checker-disable-file

-- | The universe used by default and its instances.

{-# OPTIONS -fno-warn-missing-pattern-synonym-signatures #-}
-- on 9.2.4 this is the flag that suppresses the above
-- warning
{-# OPTIONS -Wno-missing-signatures #-}
-- 9.6 notices that all the constraints on TestTypesFromTheUniverseAreAllKnown
-- are redundant (which they are), but we don't care because it only exists
-- to test that some constraints are solvable
{-# OPTIONS -Wno-redundant-constraints #-}

{-# LANGUAGE BlockArguments           #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
#include "MachDeps.h"

-- effectfully: to the best of my experimentation, -O2 here improves performance, however by
-- inspecting GHC Core I was only able to see a difference in how the 'KnownTypeIn' instance for
-- 'Int' is compiled (one more call is inlined with -O2). This needs to be investigated.
{-# OPTIONS_GHC -O2 #-}

module PlutusCore.Default.Universe
    ( DefaultUni (..)
    , pattern DefaultUniList
    , pattern DefaultUniPair
    , noMoreTypeFunctions
    , module Export  -- Re-exporting universes infrastructure for convenience.
    ) where

import PlutusCore.Builtin
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty.Extra

import Control.Applicative
import Data.Bits (toIntegralSized)
import Data.ByteString (ByteString)
import Data.Int
import Data.Proxy
import Data.Text (Text)
import Data.Word
import GHC.Exts (inline, oneShot)
import Text.Pretty
import Text.PrettyBy
import Text.PrettyBy.Fixity
import Universe as Export

{- Note [PLC types and universes]
We encode built-in types in PLC as tags for Haskell types (the latter are also called meta-types),
see Note [Universes]. A built-in type in PLC is an inhabitant of

    Some (TypeIn uni)

where @uni@ is some universe, i.e. a collection of tags that have meta-types associated with them.

A value of a built-in type is a regular Haskell value stored in

    Some (ValueOf uni)

(together with the tag associated with its type) and such a value is also called a meta-constant.

The default universe has the following constructor (pattern synonym actually):

    DefaultUniList :: !(DefaultUni a) -> DefaultUni [a]

But note that this doesn't directly lead to interop between Plutus Core and Haskell, i.e. you can't
have a meta-list whose elements are of a PLC type. You can only have a meta-list constant with
elements of a meta-type (i.e. a type from the universe).

However it is possible to apply a built-in type to an arbitrary PLC/PIR type, since we can embed
a type of an arbitrary kind into 'Type' and then apply it via 'TyApp'. But we only use it to
get polymorphic built-in functions over polymorphic built-in types, since it's not possible
to juggle values of polymorphic built-in types instantiated with non-built-in types at runtime
(it's not even possible to represent such a value in the AST, even though it's possible to represent
such a 'Type').

Finally, it is not necessary to allow embedding PLC terms into meta-constants.
We already allow built-in functions with polymorphic types. There might be a way to utilize this
feature and have meta-constructors as built-in functions.
-}

-- See Note [Representing polymorphism].
-- | The universe used by default.
data DefaultUni a where
    DefaultUniInteger :: DefaultUni (Esc Integer)
    DefaultUniByteString :: DefaultUni (Esc ByteString)
    DefaultUniString :: DefaultUni (Esc Text)
    DefaultUniUnit :: DefaultUni (Esc ())
    DefaultUniBool :: DefaultUni (Esc Bool)
    DefaultUniProtoList :: DefaultUni (Esc [])
    DefaultUniProtoPair :: DefaultUni (Esc (,))
    DefaultUniApply :: !(DefaultUni (Esc f)) -> !(DefaultUni (Esc a)) -> DefaultUni (Esc (f a))
    DefaultUniData :: DefaultUni (Esc Data)
    DefaultUniBLS12_381_G1_Element :: DefaultUni (Esc BLS12_381.G1.Element)
    DefaultUniBLS12_381_G2_Element :: DefaultUni (Esc BLS12_381.G2.Element)
    DefaultUniBLS12_381_MlResult :: DefaultUni (Esc BLS12_381.Pairing.MlResult)

-- GHC infers crazy types for these two and the straightforward ones break pattern matching,
-- so we just leave GHC with its craziness.
pattern DefaultUniList uniA =
    DefaultUniProtoList `DefaultUniApply` uniA
pattern DefaultUniPair uniA uniB =
    DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB

instance GEq DefaultUni where
    -- We define 'geq' manually instead of using 'deriveGEq', because the latter creates a single
    -- recursive definition and we want two instead. The reason why we want two is because this
    -- allows GHC to inline the initial step that appears non-recursive to GHC, because recursion
    -- is hidden in the other function that is marked as @NOINLINE@ and is chosen by GHC as a
    -- loop-breaker, see https://wiki.haskell.org/Inlining_and_Specialisation#What_is_a_loop-breaker
    -- (we're not really sure if this is a reliable solution, but if it stops working, we won't miss
    -- very much and we've failed to settle on any other approach).
    --
    -- This trick gives us a 1% speedup across validation benchmarks (some are up to 4% faster) and
    -- a more sensible generated Core where things like @geq DefaulUniBool@ are reduced away.
    geq = geqStep where
        geqStep :: DefaultUni a1 -> DefaultUni a2 -> Maybe (a1 :~: a2)
        geqStep DefaultUniInteger a2 = do
            DefaultUniInteger <- Just a2
            Just Refl
        geqStep DefaultUniByteString a2 = do
            DefaultUniByteString <- Just a2
            Just Refl
        geqStep DefaultUniString a2 = do
            DefaultUniString <- Just a2
            Just Refl
        geqStep DefaultUniUnit a2 = do
            DefaultUniUnit <- Just a2
            Just Refl
        geqStep DefaultUniBool a2 = do
            DefaultUniBool <- Just a2
            Just Refl
        geqStep DefaultUniProtoList a2 = do
            DefaultUniProtoList <- Just a2
            Just Refl
        geqStep DefaultUniProtoPair a2 = do
            DefaultUniProtoPair <- Just a2
            Just Refl
        geqStep (DefaultUniApply f1 x1) a2 = do
            DefaultUniApply f2 x2 <- Just a2
            Refl <- geqRec f1 f2
            Refl <- geqRec x1 x2
            Just Refl
        geqStep DefaultUniData a2 = do
            DefaultUniData <- Just a2
            Just Refl
        geqStep DefaultUniBLS12_381_G1_Element a2 = do
            DefaultUniBLS12_381_G1_Element <- Just a2
            Just Refl
        geqStep DefaultUniBLS12_381_G2_Element a2 = do
            DefaultUniBLS12_381_G2_Element <- Just a2
            Just Refl
        geqStep DefaultUniBLS12_381_MlResult a2 = do
            DefaultUniBLS12_381_MlResult <- Just a2
            Just Refl
        {-# INLINE geqStep #-}

        geqRec :: DefaultUni a1 -> DefaultUni a2 -> Maybe (a1 :~: a2)
        geqRec = geqStep
        {-# NOINLINE geqRec #-}

deriveGCompare ''DefaultUni

-- | For pleasing the coverage checker.
noMoreTypeFunctions :: DefaultUni (Esc (f :: a -> b -> c -> d)) -> any
noMoreTypeFunctions (f `DefaultUniApply` _) = noMoreTypeFunctions f

instance ToKind DefaultUni where
    toSingKind DefaultUniInteger              = knownKind
    toSingKind DefaultUniByteString           = knownKind
    toSingKind DefaultUniString               = knownKind
    toSingKind DefaultUniUnit                 = knownKind
    toSingKind DefaultUniBool                 = knownKind
    toSingKind DefaultUniProtoList            = knownKind
    toSingKind DefaultUniProtoPair            = knownKind
    toSingKind (DefaultUniApply uniF _)       = case toSingKind uniF of _ `SingKindArrow` cod -> cod
    toSingKind DefaultUniData                 = knownKind
    toSingKind DefaultUniBLS12_381_G1_Element = knownKind
    toSingKind DefaultUniBLS12_381_G2_Element = knownKind
    toSingKind DefaultUniBLS12_381_MlResult   = knownKind

instance HasUniApply DefaultUni where
    uniApply = DefaultUniApply

    matchUniApply (DefaultUniApply f a) _ h = h f a
    matchUniApply _                     z _ = z

deriving stock instance Show (DefaultUni a)
instance GShow DefaultUni where gshowsPrec = showsPrec

instance PrettyBy RenderContext (DefaultUni a) where
    prettyBy = inContextM $ \case
        DefaultUniInteger              -> "integer"
        DefaultUniByteString           -> "bytestring"
        DefaultUniString               -> "string"
        DefaultUniUnit                 -> "unit"
        DefaultUniBool                 -> "bool"
        DefaultUniProtoList            -> "list"
        DefaultUniProtoPair            -> "pair"
        DefaultUniApply uniF uniA      -> uniF `juxtPrettyM` uniA
        DefaultUniData                 -> "data"
        DefaultUniBLS12_381_G1_Element -> "bls12_381_G1_element"
        DefaultUniBLS12_381_G2_Element -> "bls12_381_G2_element"
        DefaultUniBLS12_381_MlResult   -> "bls12_381_mlresult"

instance PrettyBy RenderContext (SomeTypeIn DefaultUni) where
    prettyBy config (SomeTypeIn uni) = prettyBy config uni

-- | This always pretty-prints parens around type applications (e.g. @(list bool)@) and
-- doesn't pretty-print them otherwise (e.g. @integer@).
instance Pretty (DefaultUni a) where
    pretty = prettyBy juxtRenderContext
instance Pretty (SomeTypeIn DefaultUni) where
    pretty (SomeTypeIn uni) = pretty uni

-- | Elaborate a built-in type (see 'ElaborateBuiltin') from 'DefaultUni'.
type ElaborateBuiltinDefaultUni :: forall a. a -> a
type family ElaborateBuiltinDefaultUni x where
    ElaborateBuiltinDefaultUni (f x) = ElaborateBuiltinDefaultUni f `TyAppRep` x
    ElaborateBuiltinDefaultUni x     = BuiltinHead x

type instance ElaborateBuiltin DefaultUni x = ElaborateBuiltinDefaultUni x

instance (DefaultUni `Contains` f, DefaultUni `Contains` a) => DefaultUni `Contains` f a where
    knownUni = knownUni `DefaultUniApply` knownUni

instance DefaultUni `Contains` Integer where
    knownUni = DefaultUniInteger
instance DefaultUni `Contains` ByteString where
    knownUni = DefaultUniByteString
instance DefaultUni `Contains` Text where
    knownUni = DefaultUniString
instance DefaultUni `Contains` () where
    knownUni = DefaultUniUnit
instance DefaultUni `Contains` Bool where
    knownUni = DefaultUniBool
instance DefaultUni `Contains` [] where
    knownUni = DefaultUniProtoList
instance DefaultUni `Contains` (,) where
    knownUni = DefaultUniProtoPair
instance DefaultUni `Contains` Data where
    knownUni = DefaultUniData
instance DefaultUni `Contains` BLS12_381.G1.Element where
    knownUni = DefaultUniBLS12_381_G1_Element
instance DefaultUni `Contains` BLS12_381.G2.Element where
    knownUni = DefaultUniBLS12_381_G2_Element
instance DefaultUni `Contains` BLS12_381.Pairing.MlResult where
    knownUni = DefaultUniBLS12_381_MlResult

instance KnownBuiltinTypeAst tyname DefaultUni Integer =>
    KnownTypeAst tyname DefaultUni Integer
instance KnownBuiltinTypeAst tyname DefaultUni ByteString =>
    KnownTypeAst tyname DefaultUni ByteString
instance KnownBuiltinTypeAst tyname DefaultUni Text =>
    KnownTypeAst tyname DefaultUni Text
instance KnownBuiltinTypeAst tyname DefaultUni () =>
    KnownTypeAst tyname DefaultUni ()
instance KnownBuiltinTypeAst tyname DefaultUni Bool =>
    KnownTypeAst tyname DefaultUni Bool
instance KnownBuiltinTypeAst tyname DefaultUni [a] =>
    KnownTypeAst tyname DefaultUni [a]
instance KnownBuiltinTypeAst tyname DefaultUni (a, b) =>
    KnownTypeAst tyname DefaultUni (a, b)
instance KnownBuiltinTypeAst tyname DefaultUni Data =>
    KnownTypeAst tyname DefaultUni Data
instance KnownBuiltinTypeAst tyname DefaultUni BLS12_381.G1.Element =>
    KnownTypeAst tyname DefaultUni BLS12_381.G1.Element
instance KnownBuiltinTypeAst tyname DefaultUni BLS12_381.G2.Element =>
    KnownTypeAst tyname DefaultUni BLS12_381.G2.Element
instance KnownBuiltinTypeAst tyname DefaultUni BLS12_381.Pairing.MlResult =>
    KnownTypeAst tyname DefaultUni BLS12_381.Pairing.MlResult

instance KnownBuiltinTypeIn DefaultUni term Integer =>
    ReadKnownIn DefaultUni term Integer
instance KnownBuiltinTypeIn DefaultUni term ByteString =>
    ReadKnownIn DefaultUni term ByteString
instance KnownBuiltinTypeIn DefaultUni term Text =>
    ReadKnownIn DefaultUni term Text
instance KnownBuiltinTypeIn DefaultUni term () =>
    ReadKnownIn DefaultUni term ()
instance KnownBuiltinTypeIn DefaultUni term Bool =>
    ReadKnownIn DefaultUni term Bool
instance KnownBuiltinTypeIn DefaultUni term Data =>
    ReadKnownIn DefaultUni term Data
instance KnownBuiltinTypeIn DefaultUni term [a] =>
    ReadKnownIn DefaultUni term [a]
instance KnownBuiltinTypeIn DefaultUni term (a, b) =>
    ReadKnownIn DefaultUni term (a, b)
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.G1.Element =>
    ReadKnownIn DefaultUni term BLS12_381.G1.Element
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.G2.Element =>
    ReadKnownIn DefaultUni term BLS12_381.G2.Element
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.Pairing.MlResult =>
    ReadKnownIn DefaultUni term BLS12_381.Pairing.MlResult

instance KnownBuiltinTypeIn DefaultUni term Integer =>
    MakeKnownIn DefaultUni term Integer
instance KnownBuiltinTypeIn DefaultUni term ByteString =>
    MakeKnownIn DefaultUni term ByteString
instance KnownBuiltinTypeIn DefaultUni term Text =>
    MakeKnownIn DefaultUni term Text
instance KnownBuiltinTypeIn DefaultUni term () =>
    MakeKnownIn DefaultUni term ()
instance KnownBuiltinTypeIn DefaultUni term Bool =>
    MakeKnownIn DefaultUni term Bool
instance KnownBuiltinTypeIn DefaultUni term Data =>
    MakeKnownIn DefaultUni term Data
instance KnownBuiltinTypeIn DefaultUni term [a] =>
    MakeKnownIn DefaultUni term [a]
instance KnownBuiltinTypeIn DefaultUni term (a, b) =>
    MakeKnownIn DefaultUni term (a, b)
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.G1.Element =>
    MakeKnownIn DefaultUni term BLS12_381.G1.Element
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.G2.Element =>
    MakeKnownIn DefaultUni term BLS12_381.G2.Element
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.Pairing.MlResult =>
    MakeKnownIn DefaultUni term BLS12_381.Pairing.MlResult

-- If this tells you an instance is missing, add it right above, following the pattern.
instance TestTypesFromTheUniverseAreAllKnown DefaultUni

{- Note [Integral types as Integer]
Technically our universe only contains 'Integer', but many of the builtin functions that we would
like to use work over 'Int' and 'Word8'.

This is inconvenient and also error-prone: dealing with a function that takes an 'Int' or 'Word8'
means carefully downcasting the 'Integer', running the function, potentially upcasting at the end.
And it's easy to get wrong by e.g. blindly using 'fromInteger'.

Moreover, there is a latent risk here: if we *were* to build on a 32-bit architecture, then programs
which use arguments between @maxBound :: Int32@ and @maxBound :: Int64@ would behave differently!

So, what to do? We adopt the following strategy:
- We allow lifting/unlifting 'Word8' via 'Integer', including a safe downcast in 'readKnown'.
- We allow lifting/unlifting 'Int64' via 'Integer', including a safe downcast in 'readKnown'.
- We allow lifting/unlifting 'Int' via 'Int64', constraining the conversion between them to
64-bit architectures where this conversion is safe.

Doing this effectively bans builds on 32-bit systems, but that's fine, since we don't care about
supporting 32-bit systems anyway, and this way any attempts to build on them will fail fast.
-}

instance KnownTypeAst tyname DefaultUni Int64 where
    toTypeAst _ = toTypeAst $ Proxy @Integer

-- See Note [Integral types as Integer].
instance HasConstantIn DefaultUni term => MakeKnownIn DefaultUni term Int64 where
    makeKnown = makeKnown . toInteger
    {-# INLINE makeKnown #-}

instance HasConstantIn DefaultUni term => ReadKnownIn DefaultUni term Int64 where
    readKnown term =
        -- See Note [Performance of KnownTypeIn instances].
        -- Funnily, we don't need 'inline' here, unlike in the default implementation of 'readKnown'
        -- (go figure why).
        inline readKnownConstant term >>= oneShot \(i :: Integer) ->
            -- We don't make use here of `toIntegralSized` because of performance considerations,
            -- see: https://gitlab.haskell.org/ghc/ghc/-/issues/19641
            -- OPTIMIZE: benchmark an alternative `integerToIntMaybe`, modified from 'ghc-bignum'
            if fromIntegral (minBound :: Int64) <= i && i <= fromIntegral (maxBound :: Int64)
                then pure $ fromIntegral i
                else throwing_ _EvaluationFailure
    {-# INLINE readKnown #-}

#if WORD_SIZE_IN_BITS == 64
-- See Note [Integral types as Integer].

instance KnownTypeAst tyname DefaultUni Int where
    toTypeAst _ = toTypeAst $ Proxy @Integer

instance HasConstantIn DefaultUni term => MakeKnownIn DefaultUni term Int where
    -- Convert Int-to-Integer via Int64.  We could go directly `toInteger`, but this way
    -- is more explicit and it'll turn into the same thing anyway.
    -- Although this conversion is safe regardless of the CPU arch (unlike the opposite conversion),
    -- we constrain it to 64-bit for the sake of uniformity.
    makeKnown = makeKnown . fromIntegral @Int @Int64
    {-# INLINE makeKnown #-}

instance HasConstantIn DefaultUni term => ReadKnownIn DefaultUni term Int where
    -- Convert Integer-to-Int via Int64. This instance is safe only for 64-bit architecture
    -- where Int===Int64 (i.e. no truncation happening).
    readKnown term = fromIntegral @Int64 @Int <$> readKnown term
    {-# INLINE readKnown #-}
#endif

instance KnownTypeAst tyname DefaultUni Word8 where
    toTypeAst _ = toTypeAst $ Proxy @Integer

-- See Note [Integral types as Integer].
instance HasConstantIn DefaultUni term => MakeKnownIn DefaultUni term Word8 where
    makeKnown = makeKnown . toInteger
    {-# INLINE makeKnown #-}

instance HasConstantIn DefaultUni term => ReadKnownIn DefaultUni term Word8 where
    readKnown term =
        inline readKnownConstant term >>= oneShot \(i :: Integer) ->
           case toIntegralSized i of
               Just w8 -> pure w8
               _       -> throwing_ _EvaluationFailure
    {-# INLINE readKnown #-}

{- Note [Stable encoding of tags]
'encodeUni' and 'decodeUni' are used for serialisation and deserialisation of types from the
universe and we need serialised things to be extremely stable, hence the definitions of 'encodeUni'
and 'decodeUni' must be amended only in a backwards compatible manner.

See Note [Stable encoding of PLC]
-}

instance Closed DefaultUni where
    type DefaultUni `Everywhere` constr =
        ( constr `Permits` Integer
        , constr `Permits` ByteString
        , constr `Permits` Text
        , constr `Permits` ()
        , constr `Permits` Bool
        , constr `Permits` []
        , constr `Permits` (,)
        , constr `Permits` Data
        , constr `Permits` BLS12_381.G1.Element
        , constr `Permits` BLS12_381.G2.Element
        , constr `Permits` BLS12_381.Pairing.MlResult
        )

    -- See Note [Stable encoding of tags].
    -- IF YOU'RE GETTING A WARNING HERE, DON'T FORGET TO AMEND 'withDecodedUni' RIGHT BELOW.
    encodeUni DefaultUniInteger              = [0]
    encodeUni DefaultUniByteString           = [1]
    encodeUni DefaultUniString               = [2]
    encodeUni DefaultUniUnit                 = [3]
    encodeUni DefaultUniBool                 = [4]
    encodeUni DefaultUniProtoList            = [5]
    encodeUni DefaultUniProtoPair            = [6]
    encodeUni (DefaultUniApply uniF uniA)    = 7 : encodeUni uniF ++ encodeUni uniA
    encodeUni DefaultUniData                 = [8]
    encodeUni DefaultUniBLS12_381_G1_Element = [9]
    encodeUni DefaultUniBLS12_381_G2_Element = [10]
    encodeUni DefaultUniBLS12_381_MlResult   = [11]

    -- See Note [Decoding universes].
    -- See Note [Stable encoding of tags].
    withDecodedUni k = peelUniTag >>= \case
        0 -> k DefaultUniInteger
        1 -> k DefaultUniByteString
        2 -> k DefaultUniString
        3 -> k DefaultUniUnit
        4 -> k DefaultUniBool
        5 -> k DefaultUniProtoList
        6 -> k DefaultUniProtoPair
        7 ->
            withDecodedUni @DefaultUni $ \uniF ->
                withDecodedUni @DefaultUni $ \uniA ->
                    withApplicable uniF uniA $
                        k $ uniF `DefaultUniApply` uniA
        8  -> k DefaultUniData
        9  -> k DefaultUniBLS12_381_G1_Element
        10 -> k DefaultUniBLS12_381_G2_Element
        11 -> k DefaultUniBLS12_381_MlResult
        _  -> empty

    bring
        :: forall constr a r proxy. DefaultUni `Everywhere` constr
        => proxy constr -> DefaultUni (Esc a) -> (constr a => r) -> r
    bring _ DefaultUniInteger r = r
    bring _ DefaultUniByteString r = r
    bring _ DefaultUniString r = r
    bring _ DefaultUniUnit r = r
    bring _ DefaultUniBool r = r
    bring p (DefaultUniProtoList `DefaultUniApply` uniA) r =
        bring p uniA r
    bring p (DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB) r =
        bring p uniA $ bring p uniB r
    bring _ (f `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _) _ =
        noMoreTypeFunctions f
    bring _ DefaultUniData r = r
    bring _ DefaultUniBLS12_381_G1_Element r = r
    bring _ DefaultUniBLS12_381_G2_Element r = r
    bring _ DefaultUniBLS12_381_MlResult r = r
