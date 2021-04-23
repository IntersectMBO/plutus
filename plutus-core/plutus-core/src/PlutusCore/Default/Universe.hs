-- | The universe used by default and its instances.

{-# OPTIONS -fno-warn-missing-pattern-synonym-signatures #-}

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Default.Universe
    ( DefaultUni (..)
    , pattern DefaultUniList
    , pattern DefaultUniTuple
    , pattern DefaultUniString
    ) where

import           PlutusCore.Core
import           PlutusCore.Parsable
import           PlutusCore.Universe.Core

import           Control.Applicative
import qualified Data.ByteString          as BS
import           Data.Foldable
import qualified Data.Kind                as GHC
import qualified Data.Text                as Text
import           Data.Type.Equality
import           Type.Reflection

{- Note [PLC types and universes]
We encode built-in types in PLC as tags for Haskell types (the latter are also called meta-types),
see Note [Universes]. A built-in type in PLC is an inhabitant of

    Some (TypeIn uni)

where @uni@ is some universe, i.e. a collection of tags that have meta-types associated with them.

A value of a built-in type is a regular Haskell value stored in

    Some (ValueOf uni)

(together with the tag associated with its type) and such a value is also called a meta-constant.

At the moment the default universe is finite and we don't have things like

    DefaultUniList :: !(DefaultUni a) -> DefaultUni [a]

Such a type constructor can be added, but note that this doesn't directly lead to interop between
Plutus Core and Haskell, i.e. you can't have a meta-list whose elements are of a PLC type.
You can only have a meta-list constant with elements of a meta-type (i.e. a type from the universe).

Consequently, all built-in types are of kind @*@ currently.

This restriction might be fixable by adding

    DefaultUniPlc :: Type TyName DefaultUni () -> DefaultUni (Term TyName Name DefaultUni ())

to the universe (modulo exact details like 'Type'/'Term' being PLC things rather than general 'ty'
and 'term' to properly support IR, etc). But that'll require adding support to every procedure
out there (renaming, normalization, type checking, evaluation, what have you).

There might be another solution: instead of requiring universes to be of kind @* -> *@, we can allow
universes of any @k -> *@, then we'll need to establish a connection between Haskell @k@ and
a PLC 'Kind'.

data SomeK (uni :: forall k. k -> *) = forall k (a :: k). SomeK (uni a)

data AKind = forall k. AKind k

data SomeAK (uni :: AKind -> *) = forall ak. SomeAK (uni ak)

Finally, it is not necessarily the case that we need to allow embedding PLC terms into meta-constants.
We already allow built-in names with polymorphic types. There might be a way to utilize this feature
and have meta-constructors as builtin names. We still have to handle types somehow, though.
-}

-- | The universe used by default.
data DefaultUni a where
    DefaultUniInteger    :: DefaultUni Integer
    DefaultUniByteString :: DefaultUni BS.ByteString
    DefaultUniChar       :: DefaultUni Char
    DefaultUniUnit       :: DefaultUni ()
    DefaultUniBool       :: DefaultUni Bool
    DefaultUniListProto  :: DefaultUni (TypeApp [])
    DefaultUniTupleProto :: DefaultUni (TypeApp (,))
    DefaultUniApply      :: !(DefaultUni (TypeApp f)) -> !(DefaultUni a) -> DefaultUni (TypeApp (f a))
    DefaultUniRunTypeApp :: !(DefaultUni (TypeApp a)) -> DefaultUni a
    -- DefaultUniRunTypeApp :: !(DefaultUni (TypeApp (f a))) -> DefaultUni (f a)

-- GHC infers crazy types for these two and the straightforward ones break pattern matching,
-- so we just leave GHC with its craziness.
pattern DefaultUniList uniA =
    DefaultUniRunTypeApp (DefaultUniListProto `DefaultUniApply` uniA)
pattern DefaultUniTuple uniA uniB =
    DefaultUniRunTypeApp (DefaultUniTupleProto `DefaultUniApply` uniA `DefaultUniApply` uniB)

-- Just for backwards compatibility, probably should be removed at some point.
pattern DefaultUniString :: DefaultUni String
pattern DefaultUniString = DefaultUniList DefaultUniChar

instance ToKind DefaultUni where
    toKind DefaultUniInteger           = nonTypeAppKind
    toKind DefaultUniByteString        = nonTypeAppKind
    toKind DefaultUniChar              = nonTypeAppKind
    toKind DefaultUniUnit              = nonTypeAppKind
    toKind DefaultUniBool              = nonTypeAppKind
    toKind DefaultUniListProto         = typeAppToKind DefaultUniListProto
    toKind DefaultUniTupleProto        = typeAppToKind DefaultUniTupleProto
    toKind (DefaultUniApply uniF _) = case toKind uniF of
        -- We probably could avoid using @error@ here by having more type astronautics,
        -- but having @error@ should be fine for now.
        Type _            -> error "A type function can't be of type *"
        KindArrow _ _ cod -> cod
    toKind (DefaultUniRunTypeApp _)    = nonTypeAppKind

deriveGEq ''DefaultUni
deriving instance Lift (DefaultUni a)

instance HasUniApply DefaultUni where
    matchUniRunTypeApp (DefaultUniRunTypeApp a) _ h = h a
    matchUniRunTypeApp _                        z _ = z

    matchUniApply (DefaultUniApply f a) _ h = h f a
    matchUniApply _                     z _ = z

instance GShow DefaultUni where gshowsPrec = showsPrec
instance Show (DefaultUni a) where
    show DefaultUniInteger           = "integer"
    show DefaultUniByteString        = "bytestring"
    show DefaultUniChar              = "char"
    show DefaultUniUnit              = "unit"
    show DefaultUniBool              = "bool"
    show (DefaultUniRunTypeApp uniA) = show uniA
    show DefaultUniListProto         = "[]"
    show DefaultUniTupleProto        = "(,)"
    show (DefaultUniApply uniF uniB) = case uniF of
        DefaultUniListProto -> case uniB of
            DefaultUniChar -> "string"
            _              -> "[" ++ show uniB ++ "]"
        DefaultUniTupleProto -> concat ["(", show uniB, ",)"]
        DefaultUniApply DefaultUniTupleProto uniA -> concat ["(", show uniA, ",", show uniB, ")"]
        _ -> error "Impossible"

instance Parsable (Some DefaultUni) where
    parse "bool"       = Just $ Some DefaultUniBool
    parse "bytestring" = Just $ Some DefaultUniByteString
    parse "char"       = Just $ Some DefaultUniChar
    parse "integer"    = Just $ Some DefaultUniInteger
    parse "unit"       = Just $ Some DefaultUniUnit
    parse "string"     = Just $ Some DefaultUniString
    parse text         = asum
        [ do
            aT <- Text.stripPrefix "[" text >>= Text.stripSuffix "]"
            Some a <- parse aT
            Just . Some $ DefaultUniList a
        , do
            abT <- Text.stripPrefix "(" text >>= Text.stripSuffix ")"
            -- Note that we don't allow whitespace after @,@ (but we could).
            -- Anyway, looking for a single comma is just plain wrong, as we may have a nested
            -- tuple (and it can be left- or right- or both-nested), so we're running into
            -- the same parsing problem as with constants.
            case Text.splitOn "," abT of
                [aT, bT] -> do
                    Some a <- parse aT
                    Some b <- parse bT
                    Just . Some $ DefaultUniTuple a b
                _ -> Nothing
        ]

instance DefaultUni `Contains` Integer       where knownUni = DefaultUniInteger
instance DefaultUni `Contains` BS.ByteString where knownUni = DefaultUniByteString
instance DefaultUni `Contains` Char          where knownUni = DefaultUniChar
instance DefaultUni `Contains` ()            where knownUni = DefaultUniUnit
instance DefaultUni `Contains` Bool          where knownUni = DefaultUniBool

instance DefaultUni `Contains` TypeApp []  where knownUni = DefaultUniListProto
instance DefaultUni `Contains` TypeApp (,) where knownUni = DefaultUniTupleProto

instance (DefaultUni `Contains` TypeApp f, DefaultUni `Contains` a) =>
            DefaultUni `Contains` TypeApp (f a) where
    knownUni = knownUni `DefaultUniApply` knownUni

instance DefaultUni `Contains` a => DefaultUni `Contains` [a] where
    knownUni = DefaultUniList knownUni
instance (DefaultUni `Contains` a, DefaultUni `Contains` b) => DefaultUni `Contains` (a, b) where
    knownUni = DefaultUniTuple knownUni knownUni

{- Note [Stable encoding of tags]
'encodeUni' and 'decodeUni' are used for serialisation and deserialisation of types from the
universe and we need serialised things to be extremely stable, hence the definitions of 'encodeUni'
and 'decodeUni' must be amended only in a backwards compatible manner.

See Note [Stable encoding of PLC]
-}

asTypeApp
    :: forall uni ta m r. (Typeable ta, MonadFail m)
    => uni ta
    -> (forall (a :: GHC.Type). (ta ~ TypeApp a, Typeable a) => m r)
    -> m r
asTypeApp _ k = do
    App repT repA <- pure $ typeRep @ta
    let kindA = typeRepKind repA
        repT' = withTypeable kindA $ typeRep @TypeApp
    Just Refl <- pure $ repT `testEquality` repT'
    Just Refl <- pure $ typeRepKind repA `testEquality` typeRep @GHC.Type
    withTypeable repA k

withDecodeTypeAppM
    :: forall uni r. Closed uni
    => (forall (a :: GHC.Type). Typeable a => uni (TypeApp a) -> DecodeUniM r)
    -> DecodeUniM r
withDecodeTypeAppM k = withDecodeUniM @uni $ \uniTA -> asTypeApp uniTA $ k uniTA

withTypeFunRep
    :: forall uni tf m r. (Typeable tf, MonadFail m)
    => uni tf
    -> (forall k (f :: GHC.Type -> k). (tf ~ TypeApp f, Typeable k) => TypeRep f -> m r)
    -> m r
withTypeFunRep _ k = do
    App repT repF <- pure $ typeRep @tf
    let kindF = typeRepKind repF
    Fun repArg repRes <- pure kindF
    let repT' = withTypeable kindF $ typeRep @TypeApp
    Just Refl  <- pure $ repT `testEquality` repT'
    Just HRefl <- pure $ repArg `eqTypeRep` typeRep @GHC.Type
    Just Refl  <- pure $ typeRepKind repRes `testEquality` typeRep @GHC.Type
    withTypeable repRes $ k repF

asTypeFun
    :: forall uni tf m r. (Typeable tf, MonadFail m)
    => uni tf
    -> (forall k (f :: GHC.Type -> k). (tf ~ TypeApp f, Typeable k, Typeable f) => m r)
    -> m r
asTypeFun uniF k = withTypeFunRep uniF $ \repF -> withTypeable repF k

withDecodeTypeFunM
    :: forall uni r. Closed uni
    => (forall k (f :: GHC.Type -> k). (Typeable k, Typeable f) => uni (TypeApp f) -> DecodeUniM r)
    -> DecodeUniM r
withDecodeTypeFunM k = withDecodeUniM @uni $ \uniF -> asTypeFun uniF $ k uniF

instance Closed DefaultUni where
    type DefaultUni `Everywhere` constr =
        ( constr `Permits` Integer
        , constr `Permits` BS.ByteString
        , constr `Permits` Char
        , constr `Permits` ()
        , constr `Permits` Bool
        , constr `Permits` []
        , constr `Permits` (,)
        )

    -- See Note [Stable encoding of tags].
    encodeUni DefaultUniInteger           = [0]
    encodeUni DefaultUniByteString        = [1]
    encodeUni DefaultUniChar              = [2]
    encodeUni DefaultUniUnit              = [3]
    encodeUni DefaultUniBool              = [4]
    encodeUni DefaultUniListProto         = [5]
    encodeUni DefaultUniTupleProto        = [6]
    encodeUni (DefaultUniApply uniF uniA) = 7 : encodeUni uniF ++ encodeUni uniA
    encodeUni (DefaultUniRunTypeApp uniA) = 8 : encodeUni uniA

    -- See Note [Stable encoding of tags].
    withDecodeUniM k = peelUniTag >>= \case
        0 -> k DefaultUniInteger
        1 -> k DefaultUniByteString
        2 -> k DefaultUniChar
        3 -> k DefaultUniUnit
        4 -> k DefaultUniBool
        5 -> k DefaultUniListProto
        6 -> k DefaultUniTupleProto
        7 ->
            withDecodeTypeFunM $ \uniF ->
                withDecodeUniM $ \uniA ->
                    k $ uniF `DefaultUniApply` uniA
        8 -> withDecodeTypeAppM $ k . DefaultUniRunTypeApp
        _ -> empty

    bring
        :: forall constr a r proxy. DefaultUni `Everywhere` constr
        => proxy constr -> DefaultUni a -> (constr a => r) -> r
    bring _ DefaultUniInteger           r = r
    bring _ DefaultUniByteString        r = r
    bring _ DefaultUniChar              r = r
    bring _ DefaultUniUnit              r = r
    bring _ DefaultUniBool              r = r
    bring p (DefaultUniList uniA)       r = bring p uniA r
    bring p (DefaultUniTuple uniA uniB) r = bring p uniA $ bring p uniB r
    bring _ _                           _ =
        error "Can't use 'bring' for types that are not fully monomorphized"

-- >>> encodeUni (DefaultUniList (DefaultUniTuple (DefaultUniList DefaultUniInteger) DefaultUniBool))
-- [8,7,5,8,7,7,6,8,7,5,0,4]
-- >>> decodeUni [8,7,5,8,7,7,6,8,7,5,0,4] :: Maybe (Some (TypeIn DefaultUni))
-- Just (Some (TypeIn [([integer],bool)]))
