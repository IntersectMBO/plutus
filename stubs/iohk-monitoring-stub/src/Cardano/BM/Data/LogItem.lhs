
\subsection{Cardano.BM.Data.LogItem}
\label{code:Cardano.BM.Data.LogItem}

%if style == newcode
\begin{code}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NumericUnderscores #-}

module Cardano.BM.Data.LogItem
  ( LogObject (..)
  , loType
  , loType2Name
  , loTypeEq
  , LOMeta (..), mkLOMeta
  , LOContent (..)
  , locTypeEq
  , CommandValue (..)
  , LoggerName
  , MonitorAction (..)
  , PrivacyAnnotation (..)
  , PrivacyAndSeverityAnnotated (..)
  , utc2ns
  , mapLogObject
  , mapLOContent
  , loContentEq
  , loname2text
  )
  where

import           Control.Applicative (Alternative ((<|>)))
import           Control.Concurrent (myThreadId)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Aeson (FromJSON (..), ToJSON (..), Value (..), (.=),
                     (.:), object, withText, withObject)
import           Data.Aeson.Types (Object, Parser)
import           Data.Function (on)
import           Data.List (foldl')
import           Data.Maybe (fromMaybe)
import qualified Data.Text as T
import           Data.Text (Text, pack, stripPrefix)
import           Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds)
import           Data.Time.Clock (UTCTime (..), getCurrentTime)
import           Data.Word (Word64)

import           Cardano.BM.Data.Aggregated (Aggregated (..), Measurable (..))
import           Cardano.BM.Data.BackendKind
import           Cardano.BM.Data.Counter
import           Cardano.BM.Data.Severity

\end{code}
%endif

\subsubsection{LoggerName}\label{code:LoggerName}\index{LoggerName}
A |LoggerName| has currently type |Text|.
\begin{code}
type LoggerName = Text

\end{code}

\subsubsection{Logging of outcomes with |LogObject|}
\label{code:LogObject}\index{LogObject}
\label{code:LOMeta}\index{LOMeta}
\label{code:LOContent}\index{LOContent}

\begin{code}
data LogObject a = LogObject
                     { loName    :: LoggerName
                     , loMeta    :: !LOMeta
                     , loContent :: !(LOContent a)
                     } deriving (Show, Eq)

instance ToJSON a => ToJSON (LogObject a) where
    toJSON (LogObject _loname _lometa _locontent) =
        object [ "loname"    .= _loname
               , "lometa"    .= _lometa
               , "locontent" .= _locontent
               ]
instance (FromJSON a) => FromJSON (LogObject a) where
    parseJSON = withObject "LogObject" $ \v ->
                    LogObject <$> v .: "loname"
                              <*> v .: "lometa"
                              <*> v .: "locontent"

\end{code}

\label{code:mkLOMeta}\index{mkLOMeta}
Meta data for a |LogObject|.
Text was selected over ThreadId in order to be able to use the logging system
under SimM of ouroboros-network because ThreadId from Control.Concurrent lacks a Read
instance.
\begin{code}
data LOMeta = LOMeta {
                  tstamp   :: {-# UNPACK #-} !UTCTime
                , tid      :: {-# UNPACK #-} !Text
                , hostname :: {-# UNPACK #-} !Text
                , severity :: !Severity
                , privacy  :: !PrivacyAnnotation
                }

instance ToJSON LOMeta where
    toJSON (LOMeta _tstamp _tid _hn _sev _priv) =
        object [ "tstamp"   .= _tstamp
               , "tid"      .= _tid
               , "hostname" .= _hn
               , "severity" .= show _sev
               , "privacy"  .= show _priv
               ]
instance FromJSON LOMeta where
    parseJSON = withObject "LOMeta" $ \v ->
                    LOMeta <$> v .: "tstamp"
                           <*> v .: "tid"
                           <*> v .: "hostname"
                           <*> v .: "severity"
                           <*> v .: "privacy"
instance Show LOMeta where
    show (LOMeta tstamp1 tid1 hn1 _sev1 _priv1) =
        "LOMeta@" ++ show tstamp1 ++ " tid=" ++ show tid1 ++ if (not $ null $ show hn1) then " on " ++ show hn1 else ""
instance Eq LOMeta where
    (==) (LOMeta tstamp1 tid1 hn1 sev1 priv1) (LOMeta tstamp2 tid2 hn2 sev2 priv2) =
        tstamp1 == tstamp2 && tid1 == tid2 && hn1 == hn2 && sev1 == sev2 && priv1 == priv2

mkLOMeta :: MonadIO m => Severity -> PrivacyAnnotation -> m LOMeta
mkLOMeta sev priv =
    LOMeta <$> liftIO getCurrentTime
           <*> (cleantid <$> liftIO myThreadId)
           <*> pure ""
           <*> pure sev
           <*> pure priv
  where
    cleantid threadid = do
        let prefixText = "ThreadId "
            condStripPrefix s = fromMaybe s $ stripPrefix prefixText s
        condStripPrefix $ (pack . show) threadid

\end{code}

Convert a timestamp to ns since epoch:\label{code:utc2ns}\index{utc2ns}
\begin{code}
utc2ns :: UTCTime -> Word64
utc2ns utctime = fromInteger . round $ 1000_000_000 * utcTimeToPOSIXSeconds utctime

\end{code}

\begin{code}
data MonitorAction = MonitorAlert Text
                   | MonitorAlterGlobalSeverity Severity
                   | MonitorAlterSeverity LoggerName Severity
                   deriving (Show, Eq)

instance ToJSON MonitorAction where
    toJSON (MonitorAlert m) =
        object [ "kind"    .= String "MonitorAlert"
               , "message" .= toJSON m ]
    toJSON (MonitorAlterGlobalSeverity s) =
        object [ "kind"     .= String "MonitorAlterGlobalSeverity"
               , "severity" .= toJSON s ]
    toJSON (MonitorAlterSeverity n s) =
        object [ "kind" .= String "MonitorAlterSeverity"
               , "name" .= toJSON n
               , "severity" .= toJSON s ]
instance FromJSON MonitorAction where
    parseJSON = withObject "MonitorAction" $ \v ->
                    (v .: "kind" :: Parser Text)
                    >>=
                    \case "MonitorAlert" ->
                            MonitorAlert <$> v .: "message"
                          "MonitorAlterGlobalSeverity" ->
                            MonitorAlterGlobalSeverity <$> v .: "severity"
                          "MonitorAlterSeverity" ->
                            MonitorAlterSeverity <$> v .: "name" <*> v .: "severity"
                          _ -> fail "unknown MonitorAction"

\end{code}

\label{code:LogMessage}\index{LogMessage}
\label{code:LogError}\index{LogError}
\label{code:LogValue}\index{LogValue}
\label{code:LogStructured}\index{LogStructured}
\label{code:ObserveOpen}\index{ObserveOpen}
\label{code:ObserveDiff}\index{ObserveDiff}
\label{code:ObserveClose}\index{ObserveClose}
\label{code:AggregatedMessage}\index{AggregatedMessage}
\label{code:MonitoringEffect}\index{MonitoringEffect}
\label{code:Command}\index{Command}
\label{code:KillPill}\index{KillPill}

LogStructured could also be:

\begin{spec}
 forall b . (ToJSON b) => LogStructured b
\end{spec}

Payload of a |LogObject|:
\begin{code}
data LOContent a = LogMessage a
                 | LogError !Text
                 | LogValue !Text !Measurable
                 | LogStructuredText Object Text
                 | LogStructured Object
                 | ObserveOpen !CounterState
                 | ObserveDiff !CounterState
                 | ObserveClose !CounterState
                 | AggregatedMessage [(Text, Aggregated)]
                 | MonitoringEffect !MonitorAction
                 | Command !CommandValue
                 | KillPill
                 deriving (Show, Eq)
-- WARNING: update 'locTypeEq' when extending this!

instance ToJSON a => ToJSON (LOContent a) where
    toJSON (LogMessage m) =
        object [ "kind" .= String "LogMessage"
               , "message" .= toJSON m]
    toJSON (LogError m) =
        object [ "kind" .= String "LogError"
               , "message" .= toJSON m]
    toJSON (LogValue n v) =
        object [ "kind" .= String "LogValue"
               , "name" .= toJSON n
               , "value" .= toJSON v]
    toJSON (LogStructured m) =
        object [ "kind" .= String "LogStructured"
               , "data" .= m]
    toJSON (LogStructuredText o t) =
        object [ "kind" .= String "LogStructuredText"
               , "data" .= o
               , "text" .= t]
    toJSON (ObserveOpen c) =
        object [ "kind" .= String "ObserveOpen"
               , "counters" .= toJSON c]
    toJSON (ObserveDiff c) =
        object [ "kind" .= String "ObserveDiff"
               , "counters" .= toJSON c]
    toJSON (ObserveClose c) =
        object [ "kind" .= String "ObserveClose"
               , "counters" .= toJSON c ]
    toJSON (AggregatedMessage ps) =
        object [ "kind" .= String "AggregatedMessage"
               , "pairs" .= toJSON ps ]
    toJSON (MonitoringEffect a) =
        object [ "kind" .= String "MonitoringEffect"
               , "action" .= toJSON a ]
    toJSON (Command c) =
        object [ "kind" .= String "Command"
               , "command" .= toJSON c ]
    toJSON KillPill =
        String "KillPill"

instance (FromJSON a) => FromJSON (LOContent a) where
    parseJSON j = withObject "LOContent"
          (\v -> (v .: "kind" :: Parser Text)
                  >>=
                  \case "LogMessage" -> LogMessage <$> v .: "message"
                        "LogError" -> LogError <$> v .: "message"
                        "LogValue" -> LogValue <$> v .: "name" <*> v .: "value"
                        "LogStructured" -> LogStructured <$> v .: "data"
                        "LogStructuredText" -> LogStructuredText <$> v .: "data" <*> v .: "text"
                        "ObserveOpen" -> ObserveOpen <$> v .: "counters"
                        "ObserveDiff" -> ObserveDiff <$> v .: "counters"
                        "ObserveClose" -> ObserveClose <$> v .: "counters"
                        "AggregatedMessage" -> AggregatedMessage <$> v .: "pairs"
                        "MonitoringEffect" -> MonitoringEffect <$> v .: "action"
                        "Command" -> Command <$> v .: "command"
                        _ -> fail "unknown LOContent" )
          j
        <|>
          withText "LOContent"
          (\case "KillPill" -> pure KillPill
                 _ -> fail "unknown LOContent (String)")
          j

loType :: LogObject a -> Text
loType (LogObject _ _ content) = loType2Name content

-- Equality between LogObjects based on their log content types.
loTypeEq :: LogObject a -> LogObject a -> Bool
loTypeEq = locTypeEq `on` loContent

locTypeEq :: LOContent a -> LOContent a -> Bool
locTypeEq LogMessage{}        LogMessage{}        = True
locTypeEq LogError{}          LogError{}          = True
locTypeEq LogValue{}          LogValue{}          = True
locTypeEq LogStructured{}     LogStructured{}     = True
locTypeEq ObserveOpen{}       ObserveOpen{}       = True
locTypeEq ObserveDiff{}       ObserveDiff{}       = True
locTypeEq ObserveClose{}      ObserveClose{}      = True
locTypeEq AggregatedMessage{} AggregatedMessage{} = True
locTypeEq MonitoringEffect{}  MonitoringEffect{}  = True
locTypeEq Command{}           Command{}           = True
locTypeEq KillPill{}          KillPill{}          = True
locTypeEq _ _ = False

\end{code}

Name of a message content type
\begin{code}
loType2Name :: LOContent a -> Text
loType2Name = \case
    LogMessage _          -> "LogMessage"
    LogError _            -> "LogError"
    LogValue _ _          -> "LogValue"
    LogStructured _       -> "LogStructured"
    LogStructuredText _ _ -> "LogStructuredText"
    ObserveOpen _         -> "ObserveOpen"
    ObserveDiff _         -> "ObserveDiff"
    ObserveClose _        -> "ObserveClose"
    AggregatedMessage _   -> "AggregatedMessage"
    MonitoringEffect _    -> "MonitoringEffect"
    Command _             -> "Command"
    KillPill              -> "KillPill"

\end{code}

\label{code:CommandValue}\index{CommandValue}
Backends can enter commands to the trace. Commands will end up in the
|Switchboard|, which will interpret them and take action.
\begin{code}
newtype CommandValue = DumpBufferedTo BackendKind
  deriving (Show, Eq)

instance ToJSON CommandValue where
    toJSON (DumpBufferedTo be) =
        object [ "kind"    .= String "DumpBufferedTo"
               , "backend" .= toJSON be ]
instance FromJSON CommandValue where
    parseJSON = withObject "CommandValue" $ \v ->
                    (v .: "kind" :: Parser Text)
                    >>=
                    \case "DumpBufferedTo" -> DumpBufferedTo <$> v .: "backend"
                          _ -> fail "unknown CommandValue"

\end{code}

\subsubsection{Privacy annotation}
\label{code:PrivacyAnnotation}\index{PrivacyAnnotation}
\label{code:Confidential}\index{PrivacyAnnotation!Confidential}
\label{code:Public}\index{PrivacyAnnotation!Public}
\begin{code}
data PrivacyAnnotation =
      Confidential -- confidential information - handle with care
    | Public       -- indifferent - can be public.
    deriving (Show, Eq, Ord, Enum, Bounded)

instance FromJSON PrivacyAnnotation where
    parseJSON = withText "PrivacyAnnotation" $
                    \case "Confidential" -> pure Confidential
                          "Public"       -> pure Public
                          _ -> fail "unknown PrivacyAnnotation"

\end{code}

Data structure for annotating the severity and privacy of an object.
\begin{code}
data PrivacyAndSeverityAnnotated a
            = PSA { psaSeverity :: !Severity
                  , psaPrivacy  :: !PrivacyAnnotation
                  , psaPayload  :: a
                  }
            deriving (Show)

\end{code}

\subsubsection{Mapping Log Objects}
\label{code:mapLogObject}\index{mapLogObject}
\label{code:mapLOContent}\index{mapLOContent}

This provides a helper function to transform log items. It would often
be used with |contramap|.

\begin{code}
mapLogObject :: (a -> b) -> LogObject a -> LogObject b
mapLogObject f (LogObject nm me loc) = LogObject nm me (mapLOContent f loc)

instance Functor LogObject where
  fmap = mapLogObject

mapLOContent :: (a -> b) -> LOContent a -> LOContent b
mapLOContent f = \case
    LogMessage msg        -> LogMessage (f msg)
    LogError a            -> LogError a
    LogStructured o       -> LogStructured o
    LogStructuredText o m -> LogStructuredText o m
    LogValue n v          -> LogValue n v
    ObserveOpen st        -> ObserveOpen st
    ObserveDiff st        -> ObserveDiff st
    ObserveClose st       -> ObserveClose st
    AggregatedMessage ag  -> AggregatedMessage ag
    MonitoringEffect act  -> MonitoringEffect act
    Command v             -> Command v
    KillPill              -> KillPill

-- Equality between LogObjects based on their log content values.
loContentEq :: Eq a => LogObject a -> LogObject a -> Bool
loContentEq = (==) `on` loContent

\end{code}

\subsubsection{Render context name as text}
\label{code:loname2text}\index{loname2text}
\begin{code}
loname2text :: [LoggerName] -> Text
loname2text nms = T.init $ foldl' (\el acc -> acc <> "." <> el) "" nms
\end{code}
