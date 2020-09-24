-- | The universe used by default and its instances.

{-# OPTIONS_GHC -fno-warn-orphans        #-}  -- The @Pretty ByteString@ instance.
{-# OPTIONS_GHC -fno-warn-unused-matches #-}  -- Appears in generated instances.

{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Language.PlutusCore.Universe.Default
    ( DefaultUni (..)
    ) where

import           Language.PlutusCore.Universe.Core

import qualified Data.ByteString                   as BS

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
    DefaultUniString     :: DefaultUni String
    DefaultUniChar       :: DefaultUni Char
    DefaultUniUnit       :: DefaultUni ()
    DefaultUniBool       :: DefaultUni Bool

deriveGEq ''DefaultUni
deriving instance Lift (DefaultUni a)

instance GShow DefaultUni where gshowsPrec = showsPrec
instance Show (DefaultUni a) where
    show DefaultUniInteger    = "integer"
    show DefaultUniByteString = "bytestring"
    show DefaultUniString     = "string"
    show DefaultUniChar       = "char"
    show DefaultUniUnit       = "unit"
    show DefaultUniBool       = "bool"

instance DefaultUni `Includes` Integer         where knownUni = DefaultUniInteger
instance DefaultUni `Includes` BS.ByteString  where knownUni = DefaultUniByteString
instance a ~ Char => DefaultUni `Includes` [a] where knownUni = DefaultUniString
instance DefaultUni `Includes` Char            where knownUni = DefaultUniChar
instance DefaultUni `Includes` ()              where knownUni = DefaultUniUnit
instance DefaultUni `Includes` Bool            where knownUni = DefaultUniBool

{- Note [Stable encoding of tags]
'encodeUni' and 'decodeUni' are used for serialisation and deserialisation of types from the
universe and we need serialised things to be extremely stable, hence the definitions of 'encodeUni'
and 'decodeUni' must be amended only in a backwards compatible manner.

See Note [Stable encoding of PLC]
-}

instance Closed DefaultUni where
    type DefaultUni `Everywhere` constr =
        ( constr Integer
        , constr BS.ByteString
        , constr String
        , constr Char
        , constr ()
        , constr Bool
        )

    -- See Note [Stable encoding of tags].
    encodeUni DefaultUniInteger    = [0]
    encodeUni DefaultUniByteString = [1]
    encodeUni DefaultUniString     = [2]
    encodeUni DefaultUniChar       = [3]
    encodeUni DefaultUniUnit       = [4]
    encodeUni DefaultUniBool       = [5]

    -- See Note [Stable encoding of tags].
    decodeUni [0] = Just . Some $ TypeIn DefaultUniInteger
    decodeUni [1] = Just . Some $ TypeIn DefaultUniByteString
    decodeUni [2] = Just . Some $ TypeIn DefaultUniString
    decodeUni [3] = Just . Some $ TypeIn DefaultUniChar
    decodeUni [4] = Just . Some $ TypeIn DefaultUniUnit
    decodeUni [5] = Just . Some $ TypeIn DefaultUniBool
    decodeUni _   = Nothing

    bring _ DefaultUniInteger    = id
    bring _ DefaultUniByteString = id
    bring _ DefaultUniString     = id
    bring _ DefaultUniChar       = id
    bring _ DefaultUniUnit       = id
    bring _ DefaultUniBool       = id
