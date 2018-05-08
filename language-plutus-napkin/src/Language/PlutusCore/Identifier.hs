{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.PlutusCore.Identifier ( -- * Types
                                        IdentifierState
                                      , Unique (..)
                                      -- * Functions
                                      , newIdentifier
                                      , emptyIdentifierState
                                      ) where

import           Control.DeepSeq      (NFData)
import qualified Data.ByteString.Lazy as BSL
import qualified Data.IntMap          as IM
import qualified Data.Map             as M

-- | An 'IdentifierState' includes a map indexed by 'Int's as well as a map
-- indexed by 'ByteString's.
type IdentifierState = (IM.IntMap BSL.ByteString, M.Map BSL.ByteString Unique)

emptyIdentifierState :: IdentifierState
emptyIdentifierState = (mempty, mempty)

-- | A newtype wrapper for unique identifiers.
newtype Unique = Unique Int
    deriving (Show, NFData)

-- | This is a naïve implementation of interned identifiers. In particular, it
-- indexes things twice (once by 'Int', once by 'ByteString') to ensure fast
-- lookups while lexing and otherwise.
newIdentifier :: BSL.ByteString -> IdentifierState -> (Unique, IdentifierState)
newIdentifier str st@(is, ss) = case M.lookup str ss of
    Just k -> (k, st)
    Nothing -> case IM.lookupMax is of
        Just (i,_) -> (Unique $ i+1, (IM.insert (i+1) str is, M.insert str (Unique (i+1)) ss))
        Nothing    -> (Unique 0, (IM.singleton 0 str, M.singleton str (Unique 0)))
