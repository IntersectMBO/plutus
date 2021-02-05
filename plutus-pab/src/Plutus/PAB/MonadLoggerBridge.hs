{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A 'Control.Monad.Logger.Logger' instance
--   using the 'Control.Monad.Freer.Log.Log' effect
module Plutus.PAB.MonadLoggerBridge(
  MonadLoggerMsg(..)
  , TraceLoggerT(..)
  -- * Etc.
  , logStrToText
  ) where

import           Cardano.BM.Data.LogItem       (PrivacyAnnotation (Public))
import           Cardano.BM.Data.Trace         (Trace)
import           Cardano.BM.Data.Tracer        (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras (mkObjectStr)
import           Cardano.BM.Trace              (traceNamedItem)
import           Control.Monad.Catch           (MonadCatch, MonadThrow)
import qualified Control.Monad.Freer.Log       as L
import           Control.Monad.IO.Class        (MonadIO (..))
import           Control.Monad.IO.Unlift       (MonadUnliftIO (..))
import           Control.Monad.Logger          (Loc, LogLevel (..), LogSource, LogStr, MonadLogger (..), ToLogStr (..),
                                                fromLogStr)
import           Control.Monad.Reader          (ReaderT (..))
import           Data.Aeson                    (FromJSON (..), ToJSON (..), Value (Object), object, (.:), (.=))
import           Data.Aeson.Types              (typeMismatch)
import           Data.String                   (IsString (..))
import           Data.Text                     (Text)
import qualified Data.Text.Encoding            as Encoding
import           Data.Text.Prettyprint.Doc     (Pretty (..), viaShow, vsep, (<+>))
import           GHC.Generics                  (Generic)
import           Plutus.PAB.Instances          ()
import qualified Plutus.PAB.Monitoring         as M

logStrToText :: LogStr -> Text
logStrToText = Encoding.decodeUtf8 . fromLogStr -- I'm just assuming it's UTF-8...

data MonadLoggerMsg =
  MonadLoggerMsg
    { mlmLocation  :: Loc
    , mlmLogSource :: LogSource
    , mlmLogStr    :: LogStr
    }
    deriving stock (Eq, Show, Generic)

instance ToObject MonadLoggerMsg where
    toObject _ MonadLoggerMsg{mlmLocation, mlmLogSource, mlmLogStr} =
        mkObjectStr
            (logStrToText mlmLogStr)
            (mlmLocation, mlmLogSource)

instance ToJSON MonadLoggerMsg where
    toJSON MonadLoggerMsg{mlmLocation, mlmLogSource, mlmLogStr} =
        object
            [ "location" .= mlmLocation
            , "source"   .= mlmLogSource
            , "message"  .= logStrToText mlmLogStr
            ]

instance FromJSON MonadLoggerMsg where
    parseJSON (Object o) =
        MonadLoggerMsg
            <$> o .: "location"
            <*> o .: "source"
            <*> fmap fromString (o .: "message")
    parseJSON invalid = typeMismatch "Object" invalid


instance Pretty MonadLoggerMsg where
    pretty MonadLoggerMsg{mlmLocation, mlmLogSource, mlmLogStr} =
        vsep
            [ "Location:" <+> viaShow mlmLocation
            , "Source:" <+> viaShow mlmLogSource
            , "Message:" <+> viaShow mlmLogStr
            ]

toLogLevel :: LogLevel -> L.LogLevel
toLogLevel = \case
    LevelDebug   -> L.Debug
    LevelInfo    -> L.Info
    LevelWarn    -> L.Warning
    LevelError   -> L.Error
    LevelOther _ -> L.Info

-- | Interpret 'MonadLogger' effect using a 'Trace'.
-- see [note on monitoring in pab](#Main.iohk-monitoring-pab) for why this is necessary.
newtype TraceLoggerT m a = TraceLoggerT { runTraceLoggerT :: Trace m MonadLoggerMsg -> m a }
    deriving (Functor, Applicative, Monad, MonadIO, MonadCatch, MonadThrow) via (ReaderT (Trace m MonadLoggerMsg) m)

instance (MonadIO m, MonadUnliftIO m) => MonadUnliftIO (TraceLoggerT m) where
    withRunInIO inner =
        TraceLoggerT $ \trace ->
            withRunInIO $ \r ->
                inner (r . flip runTraceLoggerT trace)

instance (MonadIO m, Monad m) => MonadLogger (TraceLoggerT m) where
    monadLoggerLog l logSource ll msg = TraceLoggerT $ \trace ->
        traceNamedItem trace Public (M.toSeverity $ toLogLevel ll)
        $ MonadLoggerMsg{mlmLocation = l, mlmLogSource = logSource, mlmLogStr = toLogStr msg}
