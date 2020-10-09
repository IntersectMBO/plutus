{-| Description : Property based testing Name Utilities

This file contains various naming related utilities used for
generating Plutus Core types and terms.

-}

{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE EmptyDataDeriving   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.PlutusCore.Generators.NEAT.Common
  ( Z
  , S (..)
  , fromZ
  , NameState (nameOf)
  , emptyNameState
  , extNameState
  , TyNameState
  , tynameOf
  , emptyTyNameState
  , extTyNameState
  , mkTextNameStream
  ) where

import           Control.Enumerable
import qualified Data.Stream               as Stream
import qualified Data.Text                 as Text
import           Language.PlutusCore.Name  (Name, TyName (..))
import           Language.PlutusCore.Quote (MonadQuote (..), freshName)

-- * Enumerating deBruijn indices

data Z
  deriving (Typeable, Eq, Show)

data S n
  = FZ
  | FS n
  deriving (Typeable, Eq, Show, Functor)

instance Enumerable Z where
  enumerate = datatype []

instance Enumerable n => Enumerable (S n) where
  enumerate = share $ aconcat
    [ c0 FZ
    , c1 FS
    ]

-- |Absurd for the zero type.
fromZ :: Z -> a
fromZ i = case i of {}

-- * Namespaces

data NameState n = NameState { nameOf :: n -> Name, freshNameStrings :: Stream.Stream Text.Text }

newtype TyNameState n = TyNameState (NameState n)

tynameOf :: TyNameState n -> n -> TyName
tynameOf (TyNameState NameState{..}) i = TyName (nameOf i)

-- |Create an empty name state from a stream of text names.
emptyNameState :: Stream.Stream Text.Text -> NameState Z
emptyNameState strs = NameState { nameOf = fromZ, freshNameStrings = strs }

-- |Extend name state with a fresh name.
extNameState
  :: (MonadQuote m)
  => NameState n
  -> m (NameState (S n))
extNameState NameState{..} = liftQuote $ do
  let str = Stream.head freshNameStrings
      freshNameStrings' = Stream.tail freshNameStrings
  name <- freshName str
  let nameOf' FZ     = name
      nameOf' (FS i) = nameOf i
  return NameState { nameOf = nameOf', freshNameStrings = freshNameStrings' }

-- |Create an empty name state from a stream of text names.
emptyTyNameState :: Stream.Stream Text.Text -> TyNameState Z
emptyTyNameState strs = TyNameState (emptyNameState strs)

-- |Extend type name state with a fresh type name.
extTyNameState
  :: (MonadQuote m)
  => TyNameState n
  -> m (TyNameState (S n))
extTyNameState (TyNameState nameState) =
  TyNameState <$> extNameState nameState

-- |Create a stream of names |x0, x1, x2, ...| from a prefix |"x"|
mkTextNameStream :: Text.Text -> Stream.Stream Text.Text
mkTextNameStream prefix =
  Stream.map
    (\n -> prefix <> Text.pack (show n))
    (Stream.iterate (+1) (0 :: Integer))
