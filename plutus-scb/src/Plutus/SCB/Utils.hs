{-# LANGUAGE LambdaCase #-}

module Plutus.SCB.Utils
    ( unfoldM
    , logDebugS
    , logInfoS
    , logErrorS
    , tshow
    , render
    , liftError
    ) where

import           Control.Monad.Except            (MonadError, throwError)
import           Control.Monad.Logger            (MonadLogger, logDebugN, logErrorN, logInfoN)
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import           Options.Applicative.Help.Pretty (Pretty, displayS, pretty, renderPretty)

-- | 'unfold' in a monadic context. Invaluable for "keep doing this
-- until it says it has no more data" operations.
unfoldM :: (Monad t, Monoid m) => (b -> t (Maybe (m, b))) -> b -> t m
unfoldM f = go mempty
  where
    go xs seed = do
        v <- f seed
        case v of
            Nothing                  -> pure xs
            Just (newValue, newSeed) -> go (xs <> newValue) newSeed

logInfoS :: (MonadLogger m, Show a) => a -> m ()
logInfoS = logInfoN . tshow

logDebugS :: (MonadLogger m, Show a) => a -> m ()
logDebugS = logDebugN . tshow

logErrorS :: (MonadLogger m, Show a) => a -> m ()
logErrorS = logErrorN . tshow

tshow :: Show a => a -> Text
tshow = Text.pack . show

render :: Pretty a => a -> Text
render x = Text.pack $ displayS (renderPretty 0.4 80 (pretty x)) ""

-- | This is a lot like the 'ExceptT' constructor, except it doesn't
-- force you to accept a specific monad.
liftError :: MonadError e m => m (Either e a) -> m a
liftError action =
    action >>= \case
        Left err -> throwError err
        Right value -> pure value
