-- | The universe used by default and its instances.

{-# OPTIONS -fno-warn-missing-pattern-synonym-signatures #-}

{-# LANGUAGE ConstraintKinds       #-}
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
import           PlutusCore.Universe

import           Control.Applicative
import qualified Data.ByteString     as BS
import           Data.Foldable
import qualified Data.Text           as Text

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
    DefaultUniInteger    :: DefaultUni (T Integer)
    DefaultUniByteString :: DefaultUni (T BS.ByteString)
    DefaultUniChar       :: DefaultUni (T Char)
    DefaultUniUnit       :: DefaultUni (T ())
    DefaultUniBool       :: DefaultUni (T Bool)
    DefaultUniProtoList  :: DefaultUni (T [])
    DefaultUniProtoTuple :: DefaultUni (T (,))
    DefaultUniApply      :: !(DefaultUni (T f)) -> !(DefaultUni (T a)) -> DefaultUni (T (f a))

-- GHC infers crazy types for these two and the straightforward ones break pattern matching,
-- so we just leave GHC with its craziness.
pattern DefaultUniList uniA =
    DefaultUniProtoList `DefaultUniApply` uniA
pattern DefaultUniTuple uniA uniB =
    DefaultUniProtoTuple `DefaultUniApply` uniA `DefaultUniApply` uniB
-- Just for backwards compatibility, probably should be removed at some point.
pattern DefaultUniString = DefaultUniList DefaultUniChar

deriveGEq ''DefaultUni

instance ToKind DefaultUni where
    toKind DefaultUniInteger        = kindOf DefaultUniInteger
    toKind DefaultUniByteString     = kindOf DefaultUniByteString
    toKind DefaultUniChar           = kindOf DefaultUniChar
    toKind DefaultUniUnit           = kindOf DefaultUniUnit
    toKind DefaultUniBool           = kindOf DefaultUniBool
    toKind DefaultUniProtoList      = kindOf DefaultUniProtoList
    toKind DefaultUniProtoTuple     = kindOf DefaultUniProtoTuple
    toKind (DefaultUniApply uniF _) = case toKind uniF of
        -- We can using @error@ here by having more type astronautics with 'Typeable',
        -- but having @error@ should be fine.
        Type _            -> error "Panic: a type function can't be of type *"
        KindArrow _ _ cod -> cod

instance HasUniApply DefaultUni where
    matchUniApply (DefaultUniApply f a) _ h = h f a
    matchUniApply _                     z _ = z

instance GShow DefaultUni where gshowsPrec = showsPrec
instance Show (DefaultUni a) where
    show DefaultUniInteger           = "integer"
    show DefaultUniByteString        = "bytestring"
    show DefaultUniChar              = "char"
    show DefaultUniUnit              = "unit"
    show DefaultUniBool              = "bool"
    show DefaultUniProtoList         = "[]"
    show DefaultUniProtoTuple        = "(,)"
    show (DefaultUniApply uniF uniB) = case uniF of
        DefaultUniProtoList -> case uniB of
            DefaultUniChar -> "string"
            _              -> "[" ++ show uniB ++ "]"
        DefaultUniProtoTuple -> concat ["(", show uniB, ",)"]
        DefaultUniApply DefaultUniProtoTuple uniA -> concat ["(", show uniA, ",", show uniB, ")"]
        _ -> error "Impossible"

instance Parsable (SomeTypeIn (Kinded DefaultUni)) where
    parse "bool"       = Just . SomeTypeIn $ Kinded DefaultUniBool
    parse "bytestring" = Just . SomeTypeIn $ Kinded DefaultUniByteString
    parse "char"       = Just . SomeTypeIn $ Kinded DefaultUniChar
    parse "integer"    = Just . SomeTypeIn $ Kinded DefaultUniInteger
    parse "unit"       = Just . SomeTypeIn $ Kinded DefaultUniUnit
    parse "string"     = Just . SomeTypeIn $ Kinded DefaultUniString
    parse text         = asum
        [ do
            aT <- Text.stripPrefix "[" text >>= Text.stripSuffix "]"
            SomeTypeIn (Kinded a) <- parse aT
            Refl <- checkStar @DefaultUni a
            Just . SomeTypeIn . Kinded $ DefaultUniList a
        , do
            abT <- Text.stripPrefix "(" text >>= Text.stripSuffix ")"
            -- Note that we don't allow whitespace after @,@ (but we could).
            -- Anyway, looking for a single comma is just plain wrong, as we may have a nested
            -- tuple (and it can be left- or right- or both-nested), so we're running into
            -- the same parsing problem as with constants.
            case Text.splitOn "," abT of
                [aT, bT] -> do
                    SomeTypeIn (Kinded a) <- parse aT
                    Refl <- checkStar @DefaultUni a
                    SomeTypeIn (Kinded b) <- parse bT
                    Refl <- checkStar @DefaultUni b
                    Just . SomeTypeIn . Kinded $ DefaultUniTuple a b
                _ -> Nothing
        ]

instance DefaultUni `Contains` Integer       where knownUni = DefaultUniInteger
instance DefaultUni `Contains` BS.ByteString where knownUni = DefaultUniByteString
instance DefaultUni `Contains` Char          where knownUni = DefaultUniChar
instance DefaultUni `Contains` ()            where knownUni = DefaultUniUnit
instance DefaultUni `Contains` Bool          where knownUni = DefaultUniBool
instance DefaultUni `Contains` []            where knownUni = DefaultUniProtoList
instance DefaultUni `Contains` (,)           where knownUni = DefaultUniProtoTuple

instance (DefaultUni `Contains` f, DefaultUni `Contains` a) => DefaultUni `Contains` f a where
    knownUni = knownUni `DefaultUniApply` knownUni

{- Note [Stable encoding of tags]
'encodeUni' and 'decodeUni' are used for serialisation and deserialisation of types from the
universe and we need serialised things to be extremely stable, hence the definitions of 'encodeUni'
and 'decodeUni' must be amended only in a backwards compatible manner.

See Note [Stable encoding of PLC]
-}

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
    encodeUni DefaultUniProtoList         = [5]
    encodeUni DefaultUniProtoTuple        = [6]
    encodeUni (DefaultUniApply uniF uniA) = 7 : encodeUni uniF ++ encodeUni uniA

    -- See Note [Stable encoding of tags].
    withDecodedUni k = peelUniTag >>= \case
        0 -> k DefaultUniInteger
        1 -> k DefaultUniByteString
        2 -> k DefaultUniChar
        3 -> k DefaultUniUnit
        4 -> k DefaultUniBool
        5 -> k DefaultUniProtoList
        6 -> k DefaultUniProtoTuple
        7 ->
            withDecodedUni @DefaultUni $ \uniF ->
                withDecodedUni @DefaultUni $ \uniA ->
                    withApplicable uniF uniA $
                        k $ uniF `DefaultUniApply` uniA
        _ -> empty

    bring
        :: forall constr a r proxy. DefaultUni `Everywhere` constr
        => proxy constr -> DefaultUni (T a) -> (constr a => r) -> r
    bring _ DefaultUniInteger    r = r
    bring _ DefaultUniByteString r = r
    bring _ DefaultUniChar       r = r
    bring _ DefaultUniUnit       r = r
    bring _ DefaultUniBool       r = r
    bring p (DefaultUniProtoList `DefaultUniApply` uniA) r =
        bring p uniA r
    bring p (DefaultUniProtoTuple `DefaultUniApply` uniA `DefaultUniApply` uniB) r =
        bring p uniA $ bring p uniB r
    bring _ (f `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _) _ =
        noMoreTypeFunctions f

noMoreTypeFunctions :: DefaultUni (T (f :: a -> b -> c -> d)) -> r
noMoreTypeFunctions (f `DefaultUniApply` _) = noMoreTypeFunctions f
