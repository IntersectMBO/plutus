{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Parser.Type
    ( IdentifierState
    , newIdentifier
    , emptyIdentifierState
    , identifierStateFrom
    ) where


import PlutusCore.Name (Unique (..))

import Control.Monad.State (MonadState (get, put))
import Data.Map qualified as M
import Data.Text qualified as T

-- | An 'IdentifierState' includes a map indexed by 'Int's as well as a map
-- indexed by 'ByteString's. It is used during parsing.
type IdentifierState = (M.Map T.Text Unique, Unique)

emptyIdentifierState :: IdentifierState
emptyIdentifierState = (mempty, Unique 0)

identifierStateFrom :: Unique -> IdentifierState
identifierStateFrom u = (mempty, u)

newIdentifier :: (MonadState IdentifierState m) => T.Text -> m Unique
newIdentifier str = do
    (ss, nextU) <- get
    case M.lookup str ss of
        Just k -> pure k
        Nothing -> do
            let nextU' = Unique $ unUnique nextU + 1
            put (M.insert str nextU ss, nextU')
            pure nextU
