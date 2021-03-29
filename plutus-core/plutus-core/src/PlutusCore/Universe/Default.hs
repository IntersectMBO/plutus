{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE UndecidableSuperClasses #-}
-- | The universe used by default and its instances.

{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE OverloadedStrings       #-}
{-# LANGUAGE QuantifiedConstraints   #-}
{-# LANGUAGE TemplateHaskell         #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}

module PlutusCore.Universe.Default
    ( DefaultUni (..)
    ) where

import           PlutusCore.Parsable
import           PlutusCore.Universe.Core

import           Control.Applicative
import qualified Data.ByteString          as BS
import           Data.Foldable
import qualified Data.Text                as Text

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
    DefaultUniList       :: !(DefaultUni a) -> DefaultUni [a]
    DefaultUniTuple      :: !(DefaultUni a) -> !(DefaultUni b) -> DefaultUni (a, b)

deriveGEq ''DefaultUni
deriving instance Lift (DefaultUni a)

instance GShow DefaultUni where gshowsPrec = showsPrec
instance Show (DefaultUni a) where
    show DefaultUniInteger     = "integer"
    show DefaultUniByteString  = "bytestring"
    show DefaultUniChar        = "char"
    show DefaultUniUnit        = "unit"
    show DefaultUniBool        = "bool"
    show (DefaultUniList a)    = case a of
        DefaultUniChar -> "string"
        _              -> "[" ++ show a ++ "]"
    show (DefaultUniTuple a b) = concat ["(", show a, ",", show b, ")"]

instance Parsable (Some DefaultUni) where
    parse "bool"       = Just $ Some DefaultUniBool
    parse "bytestring" = Just $ Some DefaultUniByteString
    parse "char"       = Just $ Some DefaultUniChar
    parse "integer"    = Just $ Some DefaultUniInteger
    parse "unit"       = Just $ Some DefaultUniUnit
    parse "string"     = Just . Some $ DefaultUniList DefaultUniChar
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

instance DefaultUni `Includes` Integer       where knownUni = DefaultUniInteger
instance DefaultUni `Includes` BS.ByteString where knownUni = DefaultUniByteString
instance DefaultUni `Includes` Char          where knownUni = DefaultUniChar
instance DefaultUni `Includes` ()            where knownUni = DefaultUniUnit
instance DefaultUni `Includes` Bool          where knownUni = DefaultUniBool
instance DefaultUni `Includes` a => DefaultUni `Includes` [a] where
    knownUni = DefaultUniList knownUni
instance (DefaultUni `Includes` a, DefaultUni `Includes` b) => DefaultUni `Includes` (a, b) where
    knownUni = DefaultUniTuple knownUni knownUni

{- Note [Stable encoding of tags]
'encodeUni' and 'decodeUni' are used for serialisation and deserialisation of types from the
universe and we need serialised things to be extremely stable, hence the definitions of 'encodeUni'
and 'decodeUni' must be amended only in a backwards compatible manner.

See Note [Stable encoding of PLC]
-}

instance Closed DefaultUni where
    type DefaultUni `Everywhere` constr =
        ( constr `Accepts` Integer
        , constr `Accepts` BS.ByteString
        , constr `Accepts` Char
        , constr `Accepts` ()
        , constr `Accepts` Bool
        , constr `Accepts` []
        , constr `Accepts` (,)
        )

    -- See Note [Stable encoding of tags].
    encodeUni DefaultUniInteger     = [0]
    encodeUni DefaultUniByteString  = [1]
    encodeUni DefaultUniChar        = [2]
    encodeUni DefaultUniUnit        = [3]
    encodeUni DefaultUniBool        = [4]
    encodeUni (DefaultUniList a)    = 5 : encodeUni a
    encodeUni (DefaultUniTuple a b) = 6 : encodeUni a ++ encodeUni b

    -- See Note [Stable encoding of tags].
    decodeUniM = peelTag >>= \case
        0 -> pure . Some $ TypeIn DefaultUniInteger
        1 -> pure . Some $ TypeIn DefaultUniByteString
        2 -> pure . Some $ TypeIn DefaultUniChar
        3 -> pure . Some $ TypeIn DefaultUniUnit
        4 -> pure . Some $ TypeIn DefaultUniBool
        5 -> do
            Some (TypeIn a) <- decodeUniM
            pure . Some . TypeIn $ DefaultUniList a
        6 -> do
            Some (TypeIn a) <- decodeUniM
            Some (TypeIn b) <- decodeUniM
            pure . Some . TypeIn $ DefaultUniTuple a b
        _ -> empty

    bring _ DefaultUniInteger     r = r
    bring _ DefaultUniByteString  r = r
    bring _ DefaultUniChar        r = r
    bring _ DefaultUniUnit        r = r
    bring _ DefaultUniBool        r = r
    bring p (DefaultUniList a)    r = bring p a r
    bring p (DefaultUniTuple a b) r = bring p a $ bring p b r
