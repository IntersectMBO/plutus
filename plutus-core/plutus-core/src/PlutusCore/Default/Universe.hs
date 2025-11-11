{-# OPTIONS -fno-warn-missing-pattern-synonym-signatures #-}
-- on 9.2.4 this is the flag that suppresses the above warning
{-# OPTIONS -Wno-missing-signatures #-}
-- 9.6 notices that all the constraints on 'TestTypesFromTheUniverseAreAllKnown'
-- are redundant (which they are), but we don't care because it only exists
-- to test that some constraints are solvable
{-# OPTIONS -Wno-redundant-constraints #-}

{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE BlockArguments           #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
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
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
#include "MachDeps.h"

-- effectfully: to the best of my experimentation, -O2 here improves
-- performance, but it's not clear why. This needs to be investigated.
{-# OPTIONS_GHC -O2 #-}

-- | The universe used by default and its instances.
module PlutusCore.Default.Universe
    ( DefaultUni (..)
    , pattern DefaultUniList
    , pattern DefaultUniArray
    , pattern DefaultUniPair
    , noMoreTypeFunctions
    , module Export  -- Re-exporting universes infrastructure for convenience.
    ) where

import PlutusPrelude

import PlutusCore.Builtin
import PlutusCore.Core.Type (Type (..))
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data (Data)
import PlutusCore.Evaluation.Machine.ExMemoryUsage (IntegerCostedLiterally (..),
                                                    NumBytesCostedAsNumWords (..),
                                                    ValueLogOuterOrMaxInner (..),
                                                    ValueLogOuterSizeAddLogMaxInnerSize (..),
                                                    ValueTotalSize (..))
import PlutusCore.Pretty.Extra (juxtRenderContext)
import PlutusCore.Value (Value)

import Control.Monad.Except (throwError)
import Data.ByteString (ByteString)
import Data.Int (Int16, Int32, Int64, Int8)
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Typeable (typeRep)
import Data.Vector qualified as Vector
import Data.Vector.Strict qualified as Strict (Vector)
import Data.Word (Word16, Word32, Word64)
import GHC.Exts (inline, oneShot)
import Text.PrettyBy.Fixity (RenderContext, inContextM, juxtPrettyM)
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
    DefaultUniProtoArray :: DefaultUni (Esc Strict.Vector)
    DefaultUniProtoList :: DefaultUni (Esc [])
    DefaultUniProtoPair :: DefaultUni (Esc (,))
    DefaultUniApply :: !(DefaultUni (Esc f)) -> !(DefaultUni (Esc a)) -> DefaultUni (Esc (f a))
    DefaultUniData :: DefaultUni (Esc Data)
    DefaultUniBLS12_381_G1_Element :: DefaultUni (Esc BLS12_381.G1.Element)
    DefaultUniBLS12_381_G2_Element :: DefaultUni (Esc BLS12_381.G2.Element)
    DefaultUniBLS12_381_MlResult :: DefaultUni (Esc BLS12_381.Pairing.MlResult)
    DefaultUniValue :: DefaultUni (Esc Value)

-- GHC infers crazy types for these two and the straightforward ones break pattern matching,
-- so we just leave GHC with its craziness.
pattern DefaultUniList uniA =
    DefaultUniProtoList `DefaultUniApply` uniA
pattern DefaultUniArray uniA =
    DefaultUniProtoArray `DefaultUniApply` uniA
pattern DefaultUniPair uniA uniB =
    DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB

-- Removing 'LoopBreaker' didn't change anything at the time this comment was written, but we kept
-- it, because it hopefully provides some additional assurance that 'geqL' will not get elaborated
-- as a recursive definition.
instance AllBuiltinArgs DefaultUni (GEqL DefaultUni) a => GEqL DefaultUni a where
    geqL DefaultUniInteger a2 = do
        DefaultUniInteger <- pure a2
        pure Refl
    geqL DefaultUniByteString a2 = do
        DefaultUniByteString <- pure a2
        pure Refl
    geqL DefaultUniString a2 = do
        DefaultUniString <- pure a2
        pure Refl
    geqL DefaultUniUnit a2 = do
        DefaultUniUnit <- pure a2
        pure Refl
    geqL DefaultUniBool a2 = do
        DefaultUniBool <- pure a2
        pure Refl
    geqL (DefaultUniProtoList `DefaultUniApply` a1) listA2 = do
        DefaultUniProtoList `DefaultUniApply` a2 <- pure listA2
        Refl <- geqL (LoopBreaker a1) (LoopBreaker a2)
        pure Refl
    geqL (DefaultUniProtoArray `DefaultUniApply` a1) arrayA2 = do
        DefaultUniProtoArray `DefaultUniApply` a2 <- pure arrayA2
        Refl <- geqL (LoopBreaker a1) (LoopBreaker a2)
        pure Refl
    geqL (DefaultUniProtoPair `DefaultUniApply` a1 `DefaultUniApply` b1) pairA2 = do
        DefaultUniProtoPair `DefaultUniApply` a2 `DefaultUniApply` b2 <- pure pairA2
        Refl <- geqL (LoopBreaker a1) (LoopBreaker a2)
        Refl <- geqL (LoopBreaker b1) (LoopBreaker b2)
        pure Refl
    geqL (f `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _) _ =
        noMoreTypeFunctions f
    geqL DefaultUniData a2 = do
        DefaultUniData <- pure a2
        pure Refl
    geqL DefaultUniBLS12_381_G1_Element a2 = do
        DefaultUniBLS12_381_G1_Element <- pure a2
        pure Refl
    geqL DefaultUniBLS12_381_G2_Element a2 = do
        DefaultUniBLS12_381_G2_Element <- pure a2
        pure Refl
    geqL DefaultUniBLS12_381_MlResult a2 = do
        DefaultUniBLS12_381_MlResult <- pure a2
        pure Refl
    geqL DefaultUniValue a2 = do
        DefaultUniValue <- pure a2
        pure Refl
    {-# INLINE geqL #-}

instance GEq DefaultUni where
    -- We define 'geq' manually instead of using 'deriveGEq', because the latter creates a single
    -- recursive definition and we want two instead. The reason why we want two is because this
    -- allows GHC to inline the initial step that appears non-recursive to GHC, because recursion
    -- is hidden in the other function that is marked as @OPAQUE@ and is chosen by GHC as a
    -- loop-breaker, see https://wiki.haskell.org/Inlining_and_Specialisation#What_is_a_loop-breaker
    -- (we're not really sure if this is a reliable solution, but if it stops working, we won't miss
    -- very much and we've failed to settle on any other approach).
    --
    -- On the critical path this definition should only be used for builtins that perform equality
    -- checking of statically unknown runtime type tags ('MkCons' is one such builtin for
    -- example). All other builtins should use 'geqL' (the latter is internal to 'readKnownConstant'
    -- and is therefore hidden from the person adding a new builtin).
    --
    -- We use @NOINLINE@ instead of @OPAQUE@, because we don't actually care about the recursive
    -- definition not being inlined, we just want it to be chosen as the loop breaker.
    geq = goStep where
        goStep, goRec :: DefaultUni a1 -> DefaultUni a2 -> Maybe (a1 :~: a2)
        goStep DefaultUniInteger a2 = do
            DefaultUniInteger <- pure a2
            pure Refl
        goStep DefaultUniByteString a2 = do
            DefaultUniByteString <- pure a2
            pure Refl
        goStep DefaultUniString a2 = do
            DefaultUniString <- pure a2
            pure Refl
        goStep DefaultUniUnit a2 = do
            DefaultUniUnit <- pure a2
            pure Refl
        goStep DefaultUniBool a2 = do
            DefaultUniBool <- pure a2
            pure Refl
        goStep DefaultUniProtoList a2 = do
            DefaultUniProtoList <- pure a2
            pure Refl
        goStep DefaultUniProtoArray a2 = do
            DefaultUniProtoArray <- pure a2
            pure Refl
        goStep DefaultUniProtoPair a2 = do
            DefaultUniProtoPair <- pure a2
            pure Refl
        goStep (DefaultUniApply f1 x1) a2 = do
            DefaultUniApply f2 x2 <- pure a2
            Refl <- goRec f1 f2
            Refl <- goRec x1 x2
            pure Refl
        goStep DefaultUniData a2 = do
            DefaultUniData <- pure a2
            pure Refl
        goStep DefaultUniBLS12_381_G1_Element a2 = do
            DefaultUniBLS12_381_G1_Element <- pure a2
            pure Refl
        goStep DefaultUniBLS12_381_G2_Element a2 = do
            DefaultUniBLS12_381_G2_Element <- pure a2
            pure Refl
        goStep DefaultUniBLS12_381_MlResult a2 = do
            DefaultUniBLS12_381_MlResult <- pure a2
            pure Refl
        goStep DefaultUniValue a2 = do
            DefaultUniValue <- pure a2
            pure Refl
        {-# INLINE goStep #-}

        goRec = goStep
        {-# NOINLINE goRec #-}

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
    toSingKind DefaultUniProtoArray           = knownKind
    toSingKind DefaultUniProtoPair            = knownKind
    toSingKind (DefaultUniApply uniF _)       = case toSingKind uniF of _ `SingKindArrow` cod -> cod
    toSingKind DefaultUniData                 = knownKind
    toSingKind DefaultUniBLS12_381_G1_Element = knownKind
    toSingKind DefaultUniBLS12_381_G2_Element = knownKind
    toSingKind DefaultUniBLS12_381_MlResult   = knownKind
    toSingKind DefaultUniValue                = knownKind

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
        DefaultUniProtoArray           -> "array"
        DefaultUniProtoPair            -> "pair"
        DefaultUniApply uniF uniA      -> uniF `juxtPrettyM` uniA
        DefaultUniData                 -> "data"
        DefaultUniBLS12_381_G1_Element -> "bls12_381_G1_element"
        DefaultUniBLS12_381_G2_Element -> "bls12_381_G2_element"
        DefaultUniBLS12_381_MlResult   -> "bls12_381_mlresult"
        DefaultUniValue                -> "value"

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
instance DefaultUni `Contains` Value where
    knownUni = DefaultUniValue
instance DefaultUni `Contains` [] where
    knownUni = DefaultUniProtoList
instance DefaultUni `Contains` Strict.Vector where
    knownUni = DefaultUniProtoArray
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
instance KnownBuiltinTypeAst tyname DefaultUni (Strict.Vector a) =>
    KnownTypeAst tyname DefaultUni (Strict.Vector a)
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
instance KnownBuiltinTypeAst tyname DefaultUni Value =>
    KnownTypeAst tyname DefaultUni Value

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
instance KnownBuiltinTypeIn DefaultUni term (Strict.Vector a) =>
    ReadKnownIn DefaultUni term (Strict.Vector a)
instance KnownBuiltinTypeIn DefaultUni term (a, b) =>
    ReadKnownIn DefaultUni term (a, b)
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.G1.Element =>
    ReadKnownIn DefaultUni term BLS12_381.G1.Element
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.G2.Element =>
    ReadKnownIn DefaultUni term BLS12_381.G2.Element
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.Pairing.MlResult =>
    ReadKnownIn DefaultUni term BLS12_381.Pairing.MlResult
instance KnownBuiltinTypeIn DefaultUni term Value =>
    ReadKnownIn DefaultUni term Value

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
instance KnownBuiltinTypeIn DefaultUni term (Strict.Vector a) =>
    MakeKnownIn DefaultUni term (Strict.Vector a)
instance KnownBuiltinTypeIn DefaultUni term (a, b) =>
    MakeKnownIn DefaultUni term (a, b)
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.G1.Element =>
    MakeKnownIn DefaultUni term BLS12_381.G1.Element
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.G2.Element =>
    MakeKnownIn DefaultUni term BLS12_381.G2.Element
instance KnownBuiltinTypeIn DefaultUni term BLS12_381.Pairing.MlResult =>
    MakeKnownIn DefaultUni term BLS12_381.Pairing.MlResult
instance KnownBuiltinTypeIn DefaultUni term Value =>
    MakeKnownIn DefaultUni term Value

-- If this tells you an instance is missing, add it right above, following the pattern.
instance TestTypesFromTheUniverseAreAllKnown DefaultUni

{- Note [Integral types as Integer]
Technically our universe only contains 'Integer', but many of the builtin functions that we would
like to use work over 'Int', 'Word8' etc.

This is inconvenient and also error-prone: dealing with a function that takes an 'Int' or 'Word8'
means carefully downcasting the 'Integer', running the function, potentially upcasting at the end.
And it's easy to get wrong by e.g. blindly using 'fromInteger' or 'fromIntegral'.

Moreover, there is a latent risk here: if we *were* to build on a 32-bit architecture, then programs
which use arguments between @maxBound :: Int32@ and @maxBound :: Int64@ would behave differently!

So, what to do? We adopt the following strategy:
- We allow lifting/unlifting bounded integral types such as 'Word8' or 'Int64' via 'Integer',
  including a safe upcast in 'makeKnown' (which we could have on any architecture, but we only add
  it for 64-bit for uniformity) and a safe checked downcast in 'readKnown'.
- We allow lifting/unlifting 'Int' via 'Int64' and 'Word' via 'Word64', constraining the conversion
  between them to 64-bit architectures where this conversion is safe.

Doing this effectively bans builds on 32-bit systems, but that's fine, since we don't care about
supporting 32-bit systems anyway, and this way any attempts to build on them will fail fast.

We used to use newtype- and via-deriving for implementations of relevant instances, but at some
point GHC stopped attaching @INLINE@ annotations to those causing the GHC Core for builtins to have
multiple 'readKnown' and 'makeKnown' calls, so now we don't rely on deriving and implement instances
manually.
-}

-- | 'coerce' the argument, then call 'makeKnown'.
makeKnownCoerce
    :: forall b term a. (MakeKnownIn DefaultUni term b, Coercible a b)
    => a -> BuiltinResult term
makeKnownCoerce = coerceArg $ makeKnown @_ @_ @b
{-# INLINE makeKnownCoerce #-}

-- | Call 'readKnown', then 'coerce' the argument.
readKnownCoerce
    :: forall b term a. (ReadKnownIn DefaultUni term b, Coercible b a)
    => term -> ReadKnownM a
readKnownCoerce = fmap coerce #. readKnown @_ @_ @b
{-# INLINE readKnownCoerce #-}

-- | For deriving 'KnownTypeAst' instances via 'Integer' (no constructor, because we don't need any
-- for 'KnownTypeAst').
data AsInteger a

instance KnownTypeAst tyname DefaultUni (AsInteger a) where
    type IsBuiltin _ _ = 'False
    type ToHoles _ _ _ = '[]
    type ToBinds _ acc _ = acc
    typeAst = toTypeAst $ Proxy @Integer

makeKnownAsInteger
    :: forall term a. (KnownBuiltinTypeIn DefaultUni term Integer, Integral a)
    => a -> BuiltinResult term
makeKnownAsInteger = makeKnown . toInteger
{-# INLINE makeKnownAsInteger #-}

readKnownAsInteger
    :: forall term a.
       (KnownBuiltinTypeIn DefaultUni term Integer, Integral a, Bounded a, Typeable a)
    => term -> ReadKnownM a
readKnownAsInteger term =
    -- See Note [Performance of ReadKnownIn and MakeKnownIn instances].
    -- Funnily, we don't need 'inline' here, unlike in the default implementation of 'readKnown'
    -- (go figure why).
    inline readKnownConstant term >>= oneShot \(i :: Integer) ->
        -- We don't make use here of 'toIntegralSized' because of performance considerations,
        -- see: https://gitlab.haskell.org/ghc/ghc/-/issues/19641
        -- TODO: benchmark an alternative 'integerToIntMaybe', modified from @ghc-bignum@
        if fromIntegral (minBound :: a) <= i && i <= fromIntegral (maxBound :: a)
            then pure $ fromIntegral i
            else throwError . operationalUnliftingError $ fold
                    [ Text.pack $ show i
                    , " is not within the bounds of "
                    , Text.pack . show . typeRep $ Proxy @a
                    ]
{-# INLINE readKnownAsInteger #-}

#if WORD_SIZE_IN_BITS == 64
-- See Note [Integral types as Integer].
deriving via AsInteger Int instance
        KnownTypeAst tyname DefaultUni Int
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int where
    readKnown term = fromIntegral @Int64 @Int <$> readKnown term
    {-# INLINE readKnown #-}

deriving via AsInteger Word instance
        KnownTypeAst tyname DefaultUni Word
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word where
    readKnown term = fromIntegral @Word64 @Word <$> readKnown term
    {-# INLINE readKnown #-}
#endif

deriving via AsInteger Int8 instance
        KnownTypeAst tyname DefaultUni Int8
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int8 where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int8 where
    readKnown = readKnownAsInteger
    {-# INLINE readKnown #-}

deriving via AsInteger Int16 instance
        KnownTypeAst tyname DefaultUni Int16
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int16 where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int16 where
    readKnown = readKnownAsInteger
    {-# INLINE readKnown #-}

deriving via AsInteger Int32 instance
        KnownTypeAst tyname DefaultUni Int32
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int32 where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int32 where
    readKnown = readKnownAsInteger
    {-# INLINE readKnown #-}

deriving via AsInteger Int64 instance
        KnownTypeAst tyname DefaultUni Int64
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int64 where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int64 where
    readKnown = readKnownAsInteger
    {-# INLINE readKnown #-}

deriving via AsInteger Word8 instance
        KnownTypeAst tyname DefaultUni Word8
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word8 where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word8 where
    readKnown = readKnownAsInteger
    {-# INLINE readKnown #-}

deriving via AsInteger Word16 instance
        KnownTypeAst tyname DefaultUni Word16
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word16 where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word16 where
    readKnown = readKnownAsInteger
    {-# INLINE readKnown #-}

deriving via AsInteger Word32 instance
        KnownTypeAst tyname DefaultUni Word32
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word32 where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word32 where
    readKnown = readKnownAsInteger
    {-# INLINE readKnown #-}

deriving via AsInteger Word64 instance
        KnownTypeAst tyname DefaultUni Word64
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word64 where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word64 where
    readKnown = readKnownAsInteger
    {-# INLINE readKnown #-}

deriving newtype instance
        KnownTypeAst tyname DefaultUni NumBytesCostedAsNumWords
instance KnownBuiltinTypeIn DefaultUni term Integer =>
        MakeKnownIn DefaultUni term NumBytesCostedAsNumWords where
    makeKnown = makeKnownCoerce @Integer
    {-# INLINE makeKnown #-}

instance KnownBuiltinTypeIn DefaultUni term Integer =>
        ReadKnownIn DefaultUni term NumBytesCostedAsNumWords where
    readKnown = readKnownCoerce @Integer
    {-# INLINE readKnown #-}

deriving newtype instance
            KnownTypeAst tyname DefaultUni IntegerCostedLiterally
instance KnownBuiltinTypeIn DefaultUni term Integer =>
        MakeKnownIn DefaultUni term IntegerCostedLiterally where
    makeKnown = makeKnownCoerce @Integer
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer =>
        ReadKnownIn DefaultUni term IntegerCostedLiterally where
    readKnown = readKnownCoerce @Integer
    {-# INLINE readKnown #-}

deriving newtype instance
        KnownTypeAst tyname DefaultUni ValueTotalSize
instance KnownBuiltinTypeIn DefaultUni term Value =>
        MakeKnownIn DefaultUni term ValueTotalSize where
    makeKnown = makeKnownCoerce @Value
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Value =>
        ReadKnownIn DefaultUni term ValueTotalSize where
    readKnown = readKnownCoerce @Value
    {-# INLINE readKnown #-}

deriving newtype instance
        KnownTypeAst tyname DefaultUni ValueLogOuterOrMaxInner
instance KnownBuiltinTypeIn DefaultUni term Value =>
        MakeKnownIn DefaultUni term ValueLogOuterOrMaxInner where
    makeKnown = makeKnownCoerce @Value
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Value =>
        ReadKnownIn DefaultUni term ValueLogOuterOrMaxInner where
    readKnown = readKnownCoerce @Value
    {-# INLINE readKnown #-}

deriving newtype instance
        KnownTypeAst tyname DefaultUni ValueLogOuterSizeAddLogMaxInnerSize
instance KnownBuiltinTypeIn DefaultUni term Value =>
        MakeKnownIn DefaultUni term ValueLogOuterSizeAddLogMaxInnerSize where
    makeKnown = makeKnownCoerce @Value
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Value =>
        ReadKnownIn DefaultUni term ValueLogOuterSizeAddLogMaxInnerSize where
    readKnown = readKnownCoerce @Value
    {-# INLINE readKnown #-}

deriving via AsInteger Natural instance
        KnownTypeAst tyname DefaultUni Natural
instance KnownBuiltinTypeIn DefaultUni term Integer =>
        MakeKnownIn DefaultUni term Natural where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer =>
        ReadKnownIn DefaultUni term Natural where
    readKnown term =
        -- See Note [Performance of ReadKnownIn and MakeKnownIn instances].
        -- Funnily, we don't really need 'inline' here, unlike in the default implementation of
        -- 'readKnown' (go figure why), but we still use it just to be sure.
        inline readKnownConstant term >>= oneShot \(i :: Integer) ->
            -- TODO: benchmark alternatives:signumInteger,integerIsNegative,integerToNaturalThrow
            if i >= 0
            -- TODO: benchmark alternatives: ghc>=9 integerToNatural
            then pure $ fromInteger i
            else throwError . operationalUnliftingError $ fold
                 [ Text.pack $ show i
                 , " is not within the bounds of Natural"
                 ]
    {-# INLINE readKnown #-}

outOfBoundsErr :: Pretty a => a -> Vector.Vector term -> Text
outOfBoundsErr x branches = fold
    [ "'case "
    , display x
    , "' is out of bounds for the given number of branches: "
    , display $ Vector.length branches
    ]

instance AnnotateCaseBuiltin DefaultUni where
    annotateCaseBuiltin ty branches = case ty of
        TyBuiltin _ (SomeTypeIn DefaultUniUnit)    ->
          case branches of
            [x] -> Right $ [(x, [])]
            _   -> Left "Casing on unit only allows exactly one branch"
        TyBuiltin _ (SomeTypeIn DefaultUniBool)    ->
          case branches of
            [f]    -> Right $ [(f, [])]
            [f, t] -> Right $ [(f, []), (t, [])]
            _      -> Left "Casing on bool requires exactly one branch or two branches"
        TyBuiltin _ (SomeTypeIn DefaultUniInteger) ->
          Right $ map (, []) branches
        listTy@(TyApp _ (TyBuiltin _ (SomeTypeIn DefaultUniProtoList)) argTy) ->
          case branches of
            [cons]      -> Right [(cons, [argTy, listTy])]
            [cons, nil] -> Right [(cons, [argTy, listTy]), (nil, [])]
            _           -> Left "Casing on list requires exactly one branch or two branches"
        (TyApp _ (TyApp _ (TyBuiltin _ (SomeTypeIn DefaultUniProtoPair)) lTyArg) rTyArg) ->
          case branches of
            [f] -> Right [(f, [lTyArg, rTyArg])]
            _   -> Left "Casing on pair requires exactly one branch"
        _                 -> Left $ display (() <$ ty) <> " isn't supported in 'case'"

instance CaseBuiltin DefaultUni where
    caseBuiltin someVal@(Some (ValueOf uni x)) branches = case uni of
        DefaultUniUnit
          | 1 == len   -> Right $ HeadOnly $ branches Vector.! 0
          | otherwise -> Left $ outOfBoundsErr someVal branches
        DefaultUniBool -> case x of
            -- We allow there to be only one branch as long as the scrutinee is 'False'.
            -- This is strictly to save size by not having the 'True' branch if it was gonna be
            -- 'Error' anyway.
            False | len == 1 || len == 2 -> Right $ HeadOnly $ branches Vector.! 0
            True  |             len == 2 -> Right $ HeadOnly $ branches Vector.! 1
            _                            -> Left  $ outOfBoundsErr someVal branches
        DefaultUniInteger
            | 0 <= x && x < toInteger len -> Right $ HeadOnly $ branches Vector.! fromInteger x
            | otherwise                   -> Left  $ outOfBoundsErr someVal branches
        DefaultUniList ty
            | len == 1 ->
              case x of
                [] -> Left "Expected non-empty list, got empty list for casing list"
                (y : ys) -> Right $ headSpine (branches Vector.! 0) [someValueOf ty y, someValueOf uni ys]
            | len == 2 ->
              case x of
                []       -> Right $ HeadOnly $ branches Vector.! 1
                (y : ys) -> Right $ headSpine (branches Vector.! 0) [someValueOf ty y, someValueOf uni ys]
            | otherwise            -> Left $ outOfBoundsErr someVal branches
        DefaultUniPair tyL tyR
            | len == 1 ->
              case x of
                (l, r) -> Right $ headSpine (branches Vector.! 0) [someValueOf tyL l, someValueOf tyR r]
            | otherwise -> Left $ outOfBoundsErr someVal branches
        _ -> Left $ display uni <> " isn't supported in 'case'"
      where
        !len = Vector.length branches
    {-# INLINE caseBuiltin #-}

{- Note [Stable encoding of tags]
'encodeUni' and 'decodeUni' are used for serialisation and deserialisation of types from the
universe and we need serialised things to be extremely stable, hence the definitions of 'encodeUni'
and 'decodeUni' must be amended only in a backwards compatible manner.

See Note [Stable encoding of TPLC]
-}

instance Closed DefaultUni where
    type DefaultUni `Everywhere` constr =
        ( constr `Permits` Integer
        , constr `Permits` ByteString
        , constr `Permits` Text
        , constr `Permits` ()
        , constr `Permits` Bool
        , constr `Permits` Value
        , constr `Permits` []
        , constr `Permits` Strict.Vector
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
    encodeUni DefaultUniProtoArray           = [12]
    encodeUni DefaultUniValue                = [13]

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
        12 -> k DefaultUniProtoArray
        13 -> k DefaultUniValue
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
    bring p (DefaultUniProtoArray `DefaultUniApply` uniA) r =
        bring p uniA r
    bring p (DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB) r =
        bring p uniA $ bring p uniB r
    bring _ (f `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _) _ =
        noMoreTypeFunctions f
    bring _ DefaultUniData r = r
    bring _ DefaultUniBLS12_381_G1_Element r = r
    bring _ DefaultUniBLS12_381_G2_Element r = r
    bring _ DefaultUniBLS12_381_MlResult r = r
    bring _ DefaultUniValue r = r
