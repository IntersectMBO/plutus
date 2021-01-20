{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

module Plutus.PAB.Utils
    ( unfoldM
    , logDebugS
    , logInfoS
    , logErrorS
    , tshow
    , abbreviate
    , render
    , liftError
    , liftLocalReader
    ) where

import           Control.Monad.Except                  (MonadError, throwError)
import           Control.Monad.Logger                  (MonadLogger, logDebugN, logErrorN, logInfoN)
import           Control.Monad.Reader                  (MonadReader, ReaderT, asks, runReaderT)
import           Data.Text                             (Text)
import qualified Data.Text                             as Text
import           Data.Text.Prettyprint.Doc             (Doc, defaultLayoutOptions, layoutPretty)
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)

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

render :: Doc ann -> Text
render = renderStrict . layoutPretty defaultLayoutOptions

-- | This is a lot like the 'ExceptT' constructor, except it doesn't
-- force you to accept a specific monad.
liftError :: MonadError e m => m (Either e a) -> m a
liftError action =
    action >>= \case
        Left err    -> throwError err
        Right value -> pure value

liftLocalReader :: MonadReader f m => (f -> e) -> ReaderT e m a -> m a
liftLocalReader f action = do
    env <- asks f
    runReaderT action env

abbreviate :: Int -> Text -> Text
abbreviate n txt
    | n <= 0 = ""
    | Text.length txt > n = Text.take (n - 1) txt <> "…"
    | otherwise = txt
