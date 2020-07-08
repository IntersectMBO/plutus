{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE EmptyDataDeriving   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.PlutusCore.Gen.Common
  ( Z
  , S (..)
  , fromZ
  , NameState (nameOf)
  , emptyNameState
  , extendNameState
  , TyNameState
  , tynameOf
  , emptyTyNameState
  , extendTyNameState
  , mkTextNameStream
  ) where


import           Language.PlutusCore.Name (Name, TyName (..))
import           Language.PlutusCore.Quote (MonadQuote (..), freshName)
import           Control.Enumerable
import qualified Data.Text as Text

{-

This file contains various naming related utilities

-}


-- * Enumerating deBruijn indices

data Z
  deriving (Typeable, Eq, Show)

data S n
  = FZ
  | FS n
  deriving (Typeable, Eq, Show)

instance Enumerable Z where
  enumerate = datatype []

instance Enumerable n => Enumerable (S n) where
  enumerate = share $ aconcat
    [ c0 FZ
    , c1 FS
    ]

-- |Absurd for the zero type.
fromZ :: Z -> a
fromZ i = i `seq` error "instance of empty type Z"


-- * Namespaces

data NameState n = NameState { nameOf :: n -> Name, freshNameStrings :: [Text.Text] }

newtype TyNameState n = TyNameState (NameState n)

tynameOf :: TyNameState n -> n -> TyName
tynameOf (TyNameState NameState{..}) i = TyName (nameOf i)

-- |Create an empty name state from a stream of text names.
emptyNameState :: [Text.Text] -> NameState Z
emptyNameState strs = NameState { nameOf = fromZ, freshNameStrings = strs }

-- |Extend name state with a fresh name.
extendNameState
  :: (MonadQuote m)
  => NameState n
  -> m (NameState (S n))
extendNameState NameState{..} = liftQuote $ do
  let str = head freshNameStrings
      freshNameStrings' = tail freshNameStrings
  name <- freshName str
  let nameOf' FZ = name
      nameOf' (FS i) = nameOf i
  return NameState { nameOf = nameOf', freshNameStrings = freshNameStrings' }

-- |Create an empty name state from a stream of text names.
emptyTyNameState :: [Text.Text] -> TyNameState Z
emptyTyNameState strs = TyNameState (emptyNameState strs)

-- |Extend type name state with a fresh type name.
extendTyNameState
  :: (MonadQuote m)
  => TyNameState n
  -> m (TyNameState (S n))
extendTyNameState (TyNameState nameState) =
  TyNameState <$> extendNameState nameState

-- |Create a stream of names |x0, x1, x2, ...| from a prefix |"x"|
mkTextNameStream :: Text.Text -> [Text.Text]
mkTextNameStream prefix = [ prefix <> Text.pack (show n) | n <- [0 :: Integer ..] ]
