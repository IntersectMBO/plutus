module Language.PlutusNapkin.Identifier ( -- * Types
                                          IdentifierState
                                        -- * Functions
                                        , newIdentifier
                                        ) where

import qualified Data.ByteString.Lazy as BSL
import qualified Data.IntMap          as IM
import qualified Data.Map             as M

-- | An 'IdentifierState' includes a map indexed by 'Int's as well as a map
-- indexed by 'ByteString's.
type IdentifierState = (IM.IntMap BSL.ByteString, M.Map BSL.ByteString Int)

newIdentifier :: BSL.ByteString -> IdentifierState -> (Int, IdentifierState)
newIdentifier str st@(is, ss) = case M.lookup str ss of
    Just k -> (k, st)
    Nothing -> case IM.lookupMax is of
        Just (i,_) -> (i+1, (IM.insert (i+1) str is, M.insert str (i+1) ss))
        Nothing    -> (0, (IM.singleton 0 str, M.singleton str 0))
