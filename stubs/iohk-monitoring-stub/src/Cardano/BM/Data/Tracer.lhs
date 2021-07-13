
\subsection{Cardano.BM.Data.Tracer}
\label{code:Cardano.BM.Data.Tracer}

%if style == newcode
\begin{code}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Cardano.BM.Data.Tracer
    ( Tracer (..)
    , TracingVerbosity (..)
    , Transformable (..)
    , ToLogObject (..)
    , ToObject (..)
    , HasTextFormatter (..)
    , HasSeverityAnnotation (..)
    , HasPrivacyAnnotation (..)
    , WithSeverity (..)
    , WithPrivacyAnnotation (..)
    , contramap
    , mkObject, emptyObject
    , traceWith
    -- * tracer transformers
    , natTracer
    , nullTracer
    , stdoutTracer
    , debugTracer
    , showTracing
    , trStructured
    , trStructuredText
    -- * conditional tracing
    , condTracing
    , condTracingM
    -- * severity transformers
    , annotateSeverity
    , filterSeverity
    , setSeverity
    , severityDebug
    , severityInfo
    , severityNotice
    , severityWarning
    , severityError
    , severityCritical
    , severityAlert
    , severityEmergency
    -- * privacy annotation transformers
    , annotateConfidential
    , annotatePublic
    , annotatePrivacyAnnotation
    , filterPrivacyAnnotation
    ) where


import           Control.Monad (when)
import           Control.Monad.IO.Class (MonadIO (..))

import           Data.Aeson (Object, ToJSON (..), Value (..))
import           Data.Aeson.Text (encodeToLazyText)
import qualified Data.HashMap.Strict as HM
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import           Data.Word (Word64)

import           Cardano.BM.Data.Aggregated
import           Cardano.BM.Data.LogItem (LoggerName,
                     LogObject (..), LOContent (..), LOMeta (..),
                     PrivacyAnnotation (..), mkLOMeta)
import           Cardano.BM.Data.Severity (Severity (..))
import           Cardano.BM.Data.Trace
import           Control.Tracer

\end{code}
%endif

This module extends the basic |Tracer| with one that keeps a list of context names to
create the basis for |Trace| which accepts messages from a Tracer and ends in the |Switchboard|
for further processing of the messages.

\begin{scriptsize}
\begin{verbatim}
   +-----------------------+
   |                       |
   |    external code      |
   |                       |
   +----------+------------+
              |
              |
        +-----v-----+
        |           |
        |  Tracer   |
        |           |
        +-----+-----+
              |
              |
  +-----------v------------+
  |                        |
  |        Trace           |
  |                        |
  +-----------+------------+
              |
  +-----------v------------+
  |      Switchboard       |
  +------------------------+

  +----------+ +-----------+
  |Monitoring| |Aggregation|
  +----------+ +-----------+

          +-------+
          |Logging|
          +-------+

+-------------+ +------------+
|Visualisation| |Benchmarking|
+-------------+ +------------+

\end{verbatim}
\end{scriptsize}

\subsubsection{ToLogObject - transforms a logged item to LogObject}
\label{code:ToLogObject}\index{ToLogObject}
\label{code:toLogObject}\index{ToLogObject!toLogObject}
\label{code:toLogObject'}\index{ToLogObject!toLogObject'}
\label{code:toLogObjectVerbose}\index{ToLogObject!toLogObjectVerbose}
\label{code:toLogObjectMinimal}\index{ToLogObject!toLogObjectMinimal}

The transformer |toLogObject| accepts any type for which a |ToObject| instance
is available and returns a |LogObject| which can be forwarded into the
|Switchboard|. It adds a verbosity hint of |NormalVerbosity|.
\\
A verbosity level |TracingVerbosity| can be passed
to the transformer |toLogObject'|.


\begin{code}
class Monad m => ToLogObject m where
    toLogObject :: (ToObject a, Transformable a m b)
                => Trace m a -> Tracer m b
    toLogObject' :: (ToObject a, Transformable a m b)
                 => TracingVerbosity -> Trace m a -> Tracer m b
    toLogObjectVerbose :: (ToObject a, Transformable a m b)
                       => Trace m a -> Tracer m b
    default toLogObjectVerbose :: (ToObject a, Transformable a m b)
                       => Trace m a -> Tracer m b
    toLogObjectVerbose = trTransformer MaximalVerbosity
    toLogObjectMinimal :: (ToObject a, Transformable a m b)
                       => Trace m a -> Tracer m b
    default toLogObjectMinimal :: (ToObject a, Transformable a m b)
                       => Trace m a -> Tracer m b
    toLogObjectMinimal = trTransformer MinimalVerbosity

instance ToLogObject IO where
    toLogObject :: (MonadIO m, ToObject a, Transformable a m b)
                => Trace m a -> Tracer m b
    toLogObject = trTransformer NormalVerbosity
    toLogObject' :: (MonadIO m, ToObject a, Transformable a m b)
                 => TracingVerbosity -> Trace m a -> Tracer m b
    toLogObject' = trTransformer

\end{code}

\begin{spec}
To be placed in ouroboros-network.

instance (MonadFork m, MonadTimer m) => ToLogObject m where
    toLogObject tr = Tracer $ \a -> do
        lo <- LogObject <$> pure ""
                        <*> (LOMeta <$> getMonotonicTime  -- must be evaluated at the calling site
                                    <*> (pack . show <$> myThreadId)
                                    <*> pure Debug
                                    <*> pure Public)
                        <*> pure (LogMessage a)
        traceWith tr lo

\end{spec}

\subsubsection{Verbosity levels}
\label{code:TracingVerbosity}\index{TracingVerbosity}
\label{code:MinimalVerbosity}\index{TracingVerbosity!MinimalVerbosity}
\label{code:NormalVerbosity}\index{TracingVerbosity!NormalVerbosity}
\label{code:MaximalVerbosity}\index{TracingVerbosity!MaximalVerbosity}
The tracing verbosity will be passed to instances of |ToObject| for rendering
the traced item accordingly.
\begin{code}
data TracingVerbosity = MinimalVerbosity | NormalVerbosity | MaximalVerbosity
                        deriving (Eq, Read, Ord)

\end{code}

\subsubsection{ToObject - transforms a logged item to a JSON Object}
\label{code:ToObject}\index{ToObject}
\label{code:toObject}\index{ToObject!toObject}
Katip requires JSON objects to be logged as context. This
typeclass provides a default instance which uses |ToJSON| and
produces an empty object if 'toJSON' results in any type other than
|Object|. If you have a type you want to log that produces an Array
or Number for example, you'll want to write an explicit instance of
|ToObject|. You can trivially add a |ToObject| instance for something with
a |ToJSON| instance like:
\begin{spec}
instance ToObject Foo
\end{spec}
\\
The |toObject| function accepts a |TracingVerbosity| level as argument
and can render the traced item differently depending on the verbosity level.

\begin{code}
class ToObject a where
    toObject :: TracingVerbosity -> a -> Object
    default toObject :: ToJSON a => TracingVerbosity -> a -> Object
    toObject _ v = case toJSON v of
        Object o     -> o
        s@(String _) -> HM.singleton "string" s
        _            -> mempty
    textTransformer :: a -> Object -> Text
    default textTransformer :: a -> Object -> Text
    textTransformer _ o = TL.toStrict $ encodeToLazyText o

\end{code}

A helper function for creating an |Object| given a list of pairs, named items,
or the empty |Object|.
\label{code:mkObject}\index{mkObject}
\label{code:emptyObject}\index{emptyObject}
\begin{code}
mkObject :: ToObject a => [(Text, a)] -> HM.HashMap Text a
mkObject = HM.fromList

emptyObject :: ToObject a => HM.HashMap Text a
emptyObject = HM.empty

\end{code}

default instances:
\begin{code}
instance ToObject () where
    toObject _ _ = mempty

instance ToObject String
instance ToObject Text
instance ToObject Value
instance ToJSON a => ToObject (LogObject a)
instance ToJSON a => ToObject (LOContent a)

\end{code}

\subsubsection{A transformable Tracer}
\label{code:Transformable}\index{Transformable}
\label{code:trTransformer}\index{Transformable!trTransformer}
Parameterised over the source |Tracer| (\emph{b}) and
the target |Tracer| (\emph{a}).\\
The default definition of |trTransformer| is the |nullTracer|. This blocks output
of all items which lack a corresponding instance of |Transformable|.\\
Depending on the input type it can create objects of |LogValue| for numerical values,
|LogMessage| for textual messages, and for all others a |LogStructured| of their
|ToObject| representation.

\begin{code}
class (Monad m, HasPrivacyAnnotation b, HasSeverityAnnotation b)  => Transformable a m b where
    trTransformer :: TracingVerbosity -> Trace m a -> Tracer m b
    default trTransformer :: TracingVerbosity -> Trace m a -> Tracer m b
    trTransformer _ _ = nullTracer

trFromIntegral :: (Integral b, MonadIO m, HasPrivacyAnnotation b, HasSeverityAnnotation b)
               => LoggerName -> Trace m a -> Tracer m b
trFromIntegral name tr = Tracer $ \arg ->
        traceWith tr =<< do
            meta <- mkLOMeta (getSeverityAnnotation arg) (getPrivacyAnnotation arg)
            return ( mempty
                   , LogObject mempty meta (LogValue name $ PureI $ fromIntegral arg)
                   )

trFromReal :: (Real b, MonadIO m, HasPrivacyAnnotation b, HasSeverityAnnotation b)
           => LoggerName -> Trace m a -> Tracer m b
trFromReal name tr = Tracer $ \arg ->
        traceWith tr =<< do
            meta <- mkLOMeta (getSeverityAnnotation arg) (getPrivacyAnnotation arg)
            return ( mempty
                   , LogObject mempty meta (LogValue name $ PureD $ realToFrac arg)
                   )

instance Transformable a IO Int where
    trTransformer MinimalVerbosity = trFromIntegral ""
    trTransformer _ = trFromIntegral "int"
instance Transformable a IO Integer where
    trTransformer MinimalVerbosity = trFromIntegral ""
    trTransformer _ = trFromIntegral "integer"
instance Transformable a IO Word64 where
    trTransformer MinimalVerbosity = trFromIntegral ""
    trTransformer _ = trFromIntegral "word64"
instance Transformable a IO Double where
    trTransformer MinimalVerbosity = trFromReal ""
    trTransformer _ = trFromReal "double"
instance Transformable a IO Float where
    trTransformer MinimalVerbosity = trFromReal ""
    trTransformer _ = trFromReal "float"
instance Transformable Text IO Text where
    trTransformer _ tr = Tracer $ \arg ->
        traceWith tr =<< do
            meta <- mkLOMeta (getSeverityAnnotation arg) (getPrivacyAnnotation arg)
            return ( mempty
                   , LogObject mempty meta (LogMessage arg)
                   )
instance Transformable String IO String where
    trTransformer _ tr = Tracer $ \arg ->
        traceWith tr =<< do
            meta <- mkLOMeta (getSeverityAnnotation arg) (getPrivacyAnnotation arg)
            return ( mempty
                   , LogObject mempty meta (LogMessage arg)
                   )
instance Transformable Text IO String where
    trTransformer _ tr = Tracer $ \arg ->
        traceWith tr =<< do
            meta <- mkLOMeta (getSeverityAnnotation arg) (getPrivacyAnnotation arg)
            return ( mempty
                   , LogObject mempty meta (LogMessage $ T.pack arg)
                   )
instance Transformable String IO Text where
    trTransformer _ tr = Tracer $ \arg ->
        traceWith tr =<< do
            meta <- mkLOMeta (getSeverityAnnotation arg) (getPrivacyAnnotation arg)
            return ( mempty
                   , LogObject mempty meta (LogMessage $ T.unpack arg)
                   )

\end{code}

The function |trStructured| is a tracer transformer which transforms traced items
to their |ToObject| representation and further traces them as a |LogObject| of type
|LogStructured|. If the |ToObject| representation is empty, then no tracing happens.
\label{code:trStructured}\index{trStructured}
\begin{code}
trStructured :: (ToObject b, MonadIO m, HasPrivacyAnnotation b, HasSeverityAnnotation b)
             => TracingVerbosity -> Trace m a -> Tracer m b
trStructured verb tr = Tracer $ \arg ->
 let
   obj = toObject verb arg
 in traceWith tr =<< do
          meta <- mkLOMeta (getSeverityAnnotation arg) (getPrivacyAnnotation arg)
          return ( mempty
                 , LogObject mempty meta (LogStructuredText obj (T.pack $ show $ obj))
                 )

\end{code}


\label{code:trStructuredText}\index{trStructuredText}
\label{code:HasTextFormatter}\index{HasTextFormatter}
\begin{code}
class HasTextFormatter a where
    formatText :: a -> Object -> Text
    default formatText :: a -> Object -> Text
    formatText _a = T.pack . show

trStructuredText :: ( ToObject b, MonadIO m, HasTextFormatter b
                    , HasPrivacyAnnotation b, HasSeverityAnnotation b )
                 => TracingVerbosity -> Trace m a -> Tracer m b
trStructuredText verb tr = Tracer $ \arg ->
 let
   obj = toObject verb arg
 in traceWith tr =<< do
          meta <- mkLOMeta (getSeverityAnnotation arg) (getPrivacyAnnotation arg)
          return ( mempty
                 , LogObject mempty meta (LogStructuredText obj (formatText arg obj))
                 )

\end{code}

\subsubsection{Transformers for setting severity level}
\label{code:setSeverity}
\label{code:severityDebug}
\label{code:severityInfo}
\label{code:severityNotice}
\label{code:severityWarning}
\label{code:severityError}
\label{code:severityCritical}
\label{code:severityAlert}
\label{code:severityEmergency}
\index{setSeverity}\index{severityDebug}\index{severityInfo}
\index{severityNotice}\index{severityWarning}\index{severityError}
\index{severityCritical}\index{severityAlert}\index{severityEmergency}
The log |Severity| level of a |LogObject| can be altered.
\begin{code}
setSeverity :: Severity -> Trace m a -> Trace m a
setSeverity sev tr = Tracer $ \(ctx,lo@(LogObject _nm meta@(LOMeta _ts _tid _hn _sev _pr) _lc)) ->
                                traceWith tr $ (ctx, lo { loMeta = meta { severity = sev } })

severityDebug, severityInfo, severityNotice,
  severityWarning, severityError, severityCritical,
  severityAlert, severityEmergency  :: Trace m a -> Trace m a
severityDebug     = setSeverity Debug
severityInfo      = setSeverity Info
severityNotice    = setSeverity Notice
severityWarning   = setSeverity Warning
severityError     = setSeverity Error
severityCritical  = setSeverity Critical
severityAlert     = setSeverity Alert
severityEmergency = setSeverity Emergency

\end{code}

\label{code:annotateSeverity}\index{annotateSeverity}
The |Severity| of any |Tracer| can be set with wrapping it in |WithSeverity|.
The traced types need to be of class |HasSeverityAnnotation|.
\begin{code}
annotateSeverity :: HasSeverityAnnotation a => Tracer m (WithSeverity a) -> Tracer m a
annotateSeverity tr = Tracer $ \arg ->
    traceWith tr $ WithSeverity (getSeverityAnnotation arg) arg

\end{code}

\subsubsection{Transformers for setting privacy annotation}
\label{code:setPrivacy}
\label{code:annotateConfidential}
\label{code:annotatePublic}
\index{setPrivacy}\index{annotateConfidential}\index{annotatePublic}
The privacy annotation (|PrivacyAnnotation|) of the |LogObject| can
be altered with the following functions.
\begin{code}
setPrivacy :: PrivacyAnnotation -> Trace m a -> Trace m a
setPrivacy prannot tr = Tracer $ \(ctx,lo@(LogObject _nm meta _lc)) ->
                                   traceWith tr $ (ctx, lo { loMeta = meta { privacy = prannot }})

annotateConfidential, annotatePublic :: Trace m a -> Trace m a
annotateConfidential = setPrivacy Confidential
annotatePublic = setPrivacy Public

\end{code}

\label{code:annotatePrivacyAnnotation}\index{annotatePrivacyAnnotation}
The |PrivacyAnnotation| of any |Tracer| can be set with wrapping it in |WithPrivacyAnnotation|.
The traced types need to be of class |DefinePrivacyAnnotation|.
\begin{code}
annotatePrivacyAnnotation :: HasPrivacyAnnotation a => Tracer m (WithPrivacyAnnotation a) -> Tracer m a
annotatePrivacyAnnotation tr = Tracer $ \arg ->
    traceWith tr $ WithPrivacyAnnotation (getPrivacyAnnotation arg) arg

\end{code}

\subsubsection{Transformer for filtering based on \emph{Severity}}
\label{code:WithSeverity}\index{WithSeverity}
This structure wraps a |Severity| around traced observables.
\begin{code}
data WithSeverity a = WithSeverity Severity a

\end{code}

\label{code:filterSeverity}\index{filterSeverity}
The traced observables with annotated severity are filtered.
\begin{code}
filterSeverity :: forall m a. (Monad m, HasSeverityAnnotation a)
               => (a -> m Severity)
               -> Tracer m a
               -> Tracer m a
filterSeverity msevlimit tr = Tracer $ \arg -> do
    sevlimit <- msevlimit arg
    when (getSeverityAnnotation arg >= sevlimit) $
        traceWith tr arg

\end{code}

General instances of |WithSeverity| wrapped observable types.

\begin{code}
instance forall m a t. (Monad m, Transformable t m a) => Transformable t m (WithSeverity a) where
    trTransformer verb tr = Tracer $ \(WithSeverity sev arg) ->
        let transformer :: Tracer m a
            transformer = trTransformer verb $ setSeverity sev tr
        in traceWith transformer arg

\end{code}

\subsubsection{Transformer for filtering based on \emph{PrivacyAnnotation}}
\label{code:WithPrivacyAnnotation}\index{WithPrivacyAnnotation}
This structure wraps a |Severity| around traced observables.
\begin{code}
data WithPrivacyAnnotation a = WithPrivacyAnnotation PrivacyAnnotation a

\end{code}

\label{code:filterPrivacyAnnotation}\index{filterPrivacyAnnotation}
The traced observables with annotated severity are filtered.
\begin{code}
filterPrivacyAnnotation :: forall m a. (Monad m, HasPrivacyAnnotation a)
                        => (a -> m PrivacyAnnotation)
                        -> Tracer m a
                        -> Tracer m a
filterPrivacyAnnotation mpa tr = Tracer $ \arg -> do
    pa <- mpa arg
    when (getPrivacyAnnotation arg == pa) $
        traceWith tr arg

\end{code}

General instances of |WithPrivacyAnnotation| wrapped observable types.

\begin{code}
instance forall m a t. (Monad m, Transformable t m a) => Transformable t m (WithPrivacyAnnotation a) where
    trTransformer verb tr = Tracer $ \(WithPrivacyAnnotation pa arg) ->
        let transformer :: Tracer m a
            transformer = trTransformer verb $ setPrivacy pa tr
        in traceWith transformer arg

\end{code}

\subsubsection{The properties of being annotated with severity and privacy}
\label{code:HasSeverityAnnotation}\index{HasSeverityAnnotation}
From a type with the property of |HasSeverityAnnotation|, one will be able to
extract its severity annotation.

\begin{code}
class HasSeverityAnnotation a where
    getSeverityAnnotation :: a -> Severity
    default getSeverityAnnotation :: a -> Severity
    getSeverityAnnotation _ = Debug

instance HasSeverityAnnotation (WithSeverity a) where
    getSeverityAnnotation (WithSeverity sev _) = sev

instance HasSeverityAnnotation a => HasSeverityAnnotation (WithPrivacyAnnotation a) where
    getSeverityAnnotation (WithPrivacyAnnotation _ a) = getSeverityAnnotation a

-- default instances
instance HasSeverityAnnotation Double
instance HasSeverityAnnotation Float
instance HasSeverityAnnotation Int
instance HasSeverityAnnotation Integer
instance HasSeverityAnnotation String
instance HasSeverityAnnotation Text
instance HasSeverityAnnotation Word64

\end{code}

\label{code:HasPrivacyAnnotation}\index{HasPrivacyAnnotation}
And, privacy annotation can be extracted from types with the property |HasPrivacyAnnotation|.

\begin{code}
class HasPrivacyAnnotation a where
    getPrivacyAnnotation :: a -> PrivacyAnnotation
    default getPrivacyAnnotation :: a -> PrivacyAnnotation
    getPrivacyAnnotation _ = Public

instance HasPrivacyAnnotation (WithPrivacyAnnotation a) where
    getPrivacyAnnotation (WithPrivacyAnnotation pva _) = pva

instance HasPrivacyAnnotation a => HasPrivacyAnnotation (WithSeverity a) where
    getPrivacyAnnotation (WithSeverity _ a) = getPrivacyAnnotation a

-- default instances
instance HasPrivacyAnnotation Double
instance HasPrivacyAnnotation Float
instance HasPrivacyAnnotation Int
instance HasPrivacyAnnotation Integer
instance HasPrivacyAnnotation String
instance HasPrivacyAnnotation Text
instance HasPrivacyAnnotation Word64

\end{code}
