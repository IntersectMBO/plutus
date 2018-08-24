{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE FlexibleContexts           #-}

module Language.PlutusCore.Name ( -- * Types
                                  IdentifierState
                                , Unique (..)
                                , Name (..)
                                , TyName (..)
                                -- * Functions
                                , newIdentifier
                                , emptyIdentifierState
                                , identifierStateFrom
                                ) where

import           Control.Monad.State
import qualified Data.ByteString.Lazy as BSL
import qualified Data.IntMap          as IM
import qualified Data.Map             as M
import           Data.Text.Encoding   (decodeUtf8)
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
    deriving newtype (Eq, Functor, NFData, Pretty, Debug)

instance Eq (Name a) where
    (==) = (==) `on` nameUnique

-- | An 'IdentifierState' includes a map indexed by 'Int's as well as a map
-- indexed by 'ByteString's. It is used during parsing and renaming.
type IdentifierState = (IM.IntMap BSL.ByteString, M.Map BSL.ByteString Unique, Unique)

emptyIdentifierState :: IdentifierState
emptyIdentifierState = (mempty, mempty, Unique 0)

identifierStateFrom :: Unique -> IdentifierState
identifierStateFrom u = (mempty, mempty, u)

-- N.B. the constructors for 'Unique' are exported for the sake of the test
-- suite; I don't know if there is an easier/better way to do this
-- | A unique identifier
newtype Unique = Unique { unUnique :: Int }
    deriving (Eq, Show)
    deriving newtype NFData

-- | This is a naïve implementation of interned identifiers. In particular, it
-- indexes things twice (once by 'Int', once by 'ByteString') to ensure fast
-- lookups while lexing and otherwise.
newIdentifier :: (MonadState IdentifierState m) => BSL.ByteString -> m Unique
newIdentifier str = do
    (is, ss, nextU) <- get
    case M.lookup str ss of
        Just k -> pure k
        Nothing -> do
            let key = unUnique nextU
            let nextU' = Unique (key+1)
            put (IM.insert key str is, M.insert str nextU ss, nextU')
            pure nextU

instance Pretty (Name a) where
    pretty (Name _ s _) = pretty (decodeUtf8 (BSL.toStrict s))

instance Debug (Name a) where
    debug (Name _ s (Unique u)) = pretty (decodeUtf8 (BSL.toStrict s)) <> "_" <> pretty u
