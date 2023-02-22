{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}

module PlutusCore.Name
    ( -- * Types
      Name (..)
    , TyName (..)
    , Named (..)
    , Unique (..)
    , TypeUnique (..)
    , TermUnique (..)
    , HasText (..)
    , HasUnique (..)
    , theUnique
    , UniqueMap (..)
    -- * Functions
    , insertByUnique
    , insertByName
    , insertByNameIndex
    , insertNamed
    , fromFoldable
    , fromUniques
    , fromNames
    , lookupUnique
    , lookupName
    , lookupNameIndex
    , mapNameString
    , mapTyNameString
    , isEmpty
    ) where

import PlutusPrelude

import PlutusCore.Pretty.ConfigName

import Control.Lens
import Data.Hashable
import Data.IntMap.Strict qualified as IM
import Data.Text (Text)
import Data.Text qualified as T
import Instances.TH.Lift ()
import Language.Haskell.TH.Syntax (Lift)

-- | A 'Name' represents variables/names in Plutus Core.
data Name = Name
    { _nameText   :: T.Text -- ^ The identifier name, for use in error messages.
    , _nameUnique :: Unique
    -- ^ A 'Unique' assigned to the name, allowing for cheap comparisons in the compiler.
    }
    deriving stock (Show, Generic, Lift)
    deriving anyclass (NFData, Hashable)

-- | We use a @newtype@ to enforce separation between names used for types and
-- those used for terms.
newtype TyName = TyName { unTyName :: Name }
    deriving stock (Show, Generic, Lift)
    deriving newtype (Eq, Ord, NFData, Hashable, PrettyBy config)
instance Wrapped TyName

data Named a = Named
    { _namedString :: Text
    , _namedValue  :: a
    } deriving stock (Functor, Foldable, Traversable)

instance HasPrettyConfigName config => PrettyBy config Name where
    prettyBy config (Name txt (Unique uniq))
        | showsUnique = pretty txt <> "_" <> pretty uniq
        | otherwise   = pretty txt
        where PrettyConfigName showsUnique = toPrettyConfigName config

instance Eq Name where
    (==) = (==) `on` _nameUnique

instance Ord Name where
    (<=) = (<=) `on` _nameUnique

-- | A unique identifier
newtype Unique = Unique { unUnique :: Int }
    deriving stock (Eq, Show, Ord, Lift)
    deriving newtype (Enum, NFData, Pretty, Hashable)

-- | The unique of a type-level name.
newtype TypeUnique = TypeUnique
    { unTypeUnique :: Unique
    } deriving stock (Eq, Ord)
    deriving newtype Hashable

-- | The unique of a term-level name.
newtype TermUnique = TermUnique
    { unTermUnique :: Unique
    } deriving stock (Eq, Ord)
    deriving newtype Hashable

makeLenses 'Name

-- | Apply a function to the string representation of a 'Name'.
mapNameString :: (T.Text -> T.Text) -> Name -> Name
mapNameString = over nameText

-- | Apply a function to the string representation of a 'TyName'.
mapTyNameString :: (T.Text -> T.Text) -> TyName -> TyName
mapTyNameString = coerce mapNameString

-- | Types which have a textual name attached to them.
class HasText a where
    theText :: Lens' a Text

instance HasText Name where
    theText = nameText

instance HasText TyName where
    theText = coerced . theText @Name

-- | Types which have a 'Unique' attached to them, mostly names.
class Coercible unique Unique => HasUnique a unique | a -> unique where
    unique :: Lens' a unique
    -- | The default implementation of 'HasUnique' for newtypes.
    default unique
        :: (Wrapped a, HasUnique (Unwrapped a) unique', Coercible unique' unique)
        => Lens' a unique
    unique = _Wrapped' . unique . coerced

instance HasUnique Unique Unique where
    unique = id

instance HasUnique Name TermUnique where
    unique = nameUnique . coerced

instance HasUnique TyName TypeUnique

-- | A lens focused on the 'Unique' of a name.
theUnique :: HasUnique name unique => Lens' name Unique
theUnique = unique . coerced

-- | A mapping from uniques to values of type @a@.
newtype UniqueMap unique a = UniqueMap
    { unUniqueMap :: IM.IntMap a
    } deriving newtype (Show, Eq, Semigroup, Monoid, Functor)

-- | Insert a value by a unique.
insertByUnique :: Coercible unique Unique => unique -> a -> UniqueMap unique a -> UniqueMap unique a
insertByUnique uniq = coerce . IM.insert (coerce uniq)

-- | Insert a value by the unique of a name.
insertByName :: HasUnique name unique => name -> a -> UniqueMap unique a -> UniqueMap unique a
insertByName = insertByUnique . view unique

-- | Insert a named value by the index of the unique of the name.
insertNamed
    :: (HasText name, HasUnique name unique)
    => name
    -> a
    -> UniqueMap unique (Named a)
    -> UniqueMap unique (Named a)
insertNamed name = insertByName name . Named (name ^. theText)

-- | Insert a value by the index of the unique of a name.
-- Unlike 'insertByUnique' and 'insertByName', this function does not provide any static guarantees,
-- so you can for example insert by a type-level name in a map from term-level uniques.
insertByNameIndex
    :: (HasUnique name unique1, Coercible unique2 Unique)
    => name -> a -> UniqueMap unique2 a -> UniqueMap unique2 a
insertByNameIndex = insertByUnique . coerce . view unique

-- | Convert a 'Foldable' into a 'UniqueMap' using the given insertion function.
fromFoldable
    :: Foldable f
    => (i -> a -> UniqueMap unique a -> UniqueMap unique a) -> f (i, a) -> UniqueMap unique a
fromFoldable ins = foldl' (flip $ uncurry ins) mempty

-- | Convert a 'Foldable' with uniques into a 'UniqueMap'.
fromUniques :: Foldable f => Coercible Unique unique => f (unique, a) -> UniqueMap unique a
fromUniques = fromFoldable insertByUnique

-- | Convert a 'Foldable' with names into a 'UniqueMap'.
fromNames :: Foldable f => HasUnique name unique => f (name, a) -> UniqueMap unique a
fromNames = fromFoldable insertByName

-- | Look up a value by a unique.
lookupUnique :: Coercible unique Unique => unique -> UniqueMap unique a -> Maybe a
lookupUnique uniq = IM.lookup (coerce uniq) . unUniqueMap

-- | Look up a value by the unique of a name.
lookupName :: HasUnique name unique => name -> UniqueMap unique a -> Maybe a
lookupName = lookupUnique . view unique

-- | Look up a value by the index of the unique of a name.
-- Unlike 'lookupUnique' and 'lookupName', this function does not provide any static guarantees,
-- so you can for example look up a type-level name in a map from term-level uniques.
lookupNameIndex
    :: (HasUnique name unique1, Coercible unique2 Unique)
    => name -> UniqueMap unique2 a -> Maybe a
lookupNameIndex = lookupUnique . coerce . view unique

{-# INLINE isEmpty #-}
isEmpty :: UniqueMap unique a -> Bool
isEmpty (UniqueMap m) = IM.null m
