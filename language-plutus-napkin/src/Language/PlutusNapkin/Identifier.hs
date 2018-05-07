module Language.PlutusNapkin.Identifier ( -- * Types
                                          IdentifierState
                                        -- * Functions
                                        , newIdentifier
                                        , emptyIdentifierState
                                        ) where

import qualified Data.ByteString.Lazy as BSL
import qualified Data.IntMap          as IM
import qualified Data.Map             as M

-- | An 'IdentifierState' includes a map indexed by 'Int's as well as a map
-- indexed by 'ByteString's.
type IdentifierState = (IM.IntMap BSL.ByteString, M.Map BSL.ByteString Int)

emptyIdentifierState :: IdentifierState
emptyIdentifierState = (mempty, mempty)

-- | This is a naïve implementation of interned identifiers. In particular, it
-- indexes things twice (once by 'Int', once by 'ByteString') to ensure fast
-- lookups while lexing and otherwise.
newIdentifier :: BSL.ByteString -> IdentifierState -> (Int, IdentifierState)
newIdentifier str st@(is, ss) = case M.lookup str ss of
    Just k -> (k, st)
    Nothing -> case IM.lookupMax is of
        Just (i,_) -> (i+1, (IM.insert (i+1) str is, M.insert str (i+1) ss))
        Nothing    -> (0, (IM.singleton 0 str, M.singleton str 0))
