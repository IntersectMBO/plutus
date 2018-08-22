{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}

module Language.PlutusCore.Name ( -- * Types
                                  IdentifierState
                                , Unique (..)
                                , Name (..)
                                , TyName (..)
                                -- * Functions
                                , newIdentifier
                                , emptyIdentifierState
                                , freshName
                                , freshTyName
                                ) where

import qualified Data.ByteString.Lazy          as BSL
import qualified Data.IntMap                   as IM
import qualified Data.Map                      as M
import           Data.Text.Encoding            (decodeUtf8)
import           Language.PlutusCore.PrettyCfg
import           PlutusPrelude

-- | A 'Name' represents variables/names in Plutus Core.
data Name a = Name { nameAttribute :: a
                   , nameString    :: BSL.ByteString -- ^ The identifier name, for use in error messages.
                   , nameUnique    :: Unique -- ^ A 'Unique' assigned to the name during lexing, allowing for cheap comparisons in the compiler.
                   }
            deriving (Functor, Show, Generic, NFData)

-- | We use a @newtype@ to enforce separation between names used for types and
-- those used for terms.
newtype TyName a = TyName { unTyName :: Name a }
    deriving Show
    deriving newtype (Eq, Functor, NFData, PrettyCfg)

instance Eq (Name a) where
    (==) = (==) `on` nameUnique

-- | An 'IdentifierState' includes a map indexed by 'Int's as well as a map
-- indexed by 'ByteString's. It is used during parsing and renaming.
type IdentifierState = (IM.IntMap BSL.ByteString, M.Map BSL.ByteString Unique)

emptyIdentifierState :: IdentifierState
emptyIdentifierState = (mempty, mempty)

-- N.B. the constructors for 'Unique' are exported for the sake of the test
-- suite; I don't know if there is an easier/better way to do this
-- | A unique identifier
newtype Unique = Unique { unUnique :: Int }
    deriving (Eq, Show)
    deriving newtype NFData

-- | This is a naïve implementation of interned identifiers. In particular, it
-- indexes things twice (once by 'Int', once by 'ByteString') to ensure fast
-- lookups while lexing and otherwise.
newIdentifier :: BSL.ByteString -> IdentifierState -> (Unique, IdentifierState)
newIdentifier str st@(is, ss) = case M.lookup str ss of
    Just k -> (k, st)
    Nothing -> case IM.maxViewWithKey is of
        Just ((i,_), _) -> (Unique (i+1), (IM.insert (i+1) str is, M.insert str (Unique (i+1)) ss))
        Nothing         -> (Unique 0, (IM.singleton 0 str, M.singleton str (Unique 0)))

freshName :: a -> BSL.ByteString -> Fresh (Name a)
freshName attr name = Name attr name . Unique <$> freshInt

freshTyName :: a -> BSL.ByteString -> Fresh (TyName a)
freshTyName = fmap TyName .* freshName

instance PrettyCfg (Name s) where
    prettyCfg (Configuration False _) (Name _ s _)         = pretty (decodeUtf8 (BSL.toStrict s))
    prettyCfg (Configuration True _) (Name _ s (Unique u)) = pretty (decodeUtf8 (BSL.toStrict s)) <> "_" <> pretty u
