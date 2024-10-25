{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}

module PlutusTx.Data.List (
    List,
    find,
    findIndices,
    filter,
    mapMaybe,
    any,
    foldMap,
) where

import PlutusTx.Builtins.Internal (BuiltinList, mkList, unsafeDataAsList)
import PlutusTx.IsData.Class (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude hiding (any, filter, find, findIndices, foldMap, mapMaybe)
import Prettyprinter (Pretty (..))

import Prelude qualified as Haskell

newtype List a = List (BuiltinList BuiltinData)
  deriving stock (Haskell.Show, Haskell.Eq)

instance Eq (List a) where
    List l == List l' = Haskell.undefined

instance ToData (List a) where
    toBuiltinData (List l) = mkList l

instance FromData (List a) where
    fromBuiltinData = Just . List . unsafeDataAsList

instance UnsafeFromData (List a) where
    unsafeFromBuiltinData = List . unsafeDataAsList

instance Pretty (List a) where
    pretty = Haskell.undefined

find = Haskell.undefined

findIndices = Haskell.undefined

filter = Haskell.undefined

mapMaybe = Haskell.undefined

any = Haskell.undefined

foldMap = Haskell.undefined

makeLift ''List
