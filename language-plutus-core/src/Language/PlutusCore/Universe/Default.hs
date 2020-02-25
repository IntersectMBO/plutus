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

import           Language.PlutusCore.Pretty.Utils
import           Language.PlutusCore.Universe.Core

import qualified Data.ByteString.Lazy              as BSL
import           Data.GADT.Compare.TH
import           Data.Text.Prettyprint.Doc
import           Language.Haskell.TH.Syntax

instance Pretty BSL.ByteString where
    pretty = prettyBytes

{- Note [PLC types and universes]
At the moment the default universe is finite and we don't have things like

    DefaultUniList :: !(DefaultUni a) -> DefaultUni [a]

Such a type constructor can be added, but note that this doesn't directly lead to interop between
Plutus Core and Haskell, i.e. you can't have a meta-list whose elements are of a PLC type.
You can only have a meta-list constant with elements of a meta-type (i.e. a type from the universe).
This restriction might be fixable by adding

    DefaultUniPlc :: Type TyName DefaultUni () -> DefaultUni (Term TyName Name DefaultUni ())

to the universe (modulo exact details like 'Type'/'Term' being PLC things rather than general 'ty'
and 'term' to properly support IR, etc). But that'll require adding support to every procedure
out there (renaming, normalization, type checking, evaluation, what have you).

There might be another solution: instead of requiring universes to be of kind @* -> *@, we can allow
universes of any @k -> *@, then we'll need to establish a connection between Haskell @k@ and
a PLC 'Kind'.

Finally, it is not necessarily the case that we need to allow embedding PLC terms into meta-constants.
We already allow builtin names with polymorphic types. There might be a way to utilize this feature
and have meta-constructors as builtin names. We still have to handle types somehow, though.
-}

-- | The universe used by default.
data DefaultUni a where
    DefaultUniInteger    :: DefaultUni Integer
    DefaultUniByteString :: DefaultUni BSL.ByteString
    DefaultUniString     :: DefaultUni String

deriveGEq ''DefaultUni
deriving instance Lift (DefaultUni a)
instance GLift DefaultUni

instance GShow DefaultUni where gshowsPrec = showsPrec
instance Show (DefaultUni a) where
    show DefaultUniInteger    = "integer"
    show DefaultUniByteString = "bytestring"
    show DefaultUniString     = "string"

instance DefaultUni `Includes` Integer         where knownUni = DefaultUniInteger
instance DefaultUni `Includes` BSL.ByteString  where knownUni = DefaultUniByteString
instance a ~ Char => DefaultUni `Includes` [a] where knownUni = DefaultUniString

instance Closed DefaultUni where
    type DefaultUni `Everywhere` constr =
        ( constr Integer
        , constr BSL.ByteString
        , constr String
        )

    tagOf DefaultUniInteger    = 0
    tagOf DefaultUniByteString = 1
    tagOf DefaultUniString     = 2

    uniAt 0 = Just . Some $ In DefaultUniInteger
    uniAt 1 = Just . Some $ In DefaultUniByteString
    uniAt 2 = Just . Some $ In DefaultUniString
    uniAt _ = Nothing

    bring _ DefaultUniInteger    = id
    bring _ DefaultUniByteString = id
    bring _ DefaultUniString     = id
