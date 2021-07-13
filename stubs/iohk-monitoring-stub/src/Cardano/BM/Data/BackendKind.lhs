
\subsection{Cardano.BM.Data.BackendKind}
\label{code:Cardano.BM.Data.BackendKind}

%if style == newcode
\begin{code}
{-# LANGUAGE LambdaCase #-}

module Cardano.BM.Data.BackendKind
  ( BackendKind (..)
  )
  where

import           Control.Applicative (Alternative ((<|>)))
import           Data.Aeson (FromJSON (..), ToJSON (..), Value (..), (.=),
                     (.:), object, withText, withObject)
import           Data.Aeson.Types (Parser)
import           Data.Text (Text)

\end{code}
%endif

\subsubsection{BackendKind}\label{code:BackendKind}\index{BackendKind}
\label{code:AggregationBK}\index{BackendKind!AggregationBK}
\label{code:EditorBK}\index{BackendKind!EditorBK}
\label{code:EKGViewBK}\index{BackendKind!EKGViewBK}
\label{code:GraylogBK}\index{BackendKind!GraylogBK}
\label{code:KatipBK}\index{BackendKind!KatipBK}
\label{code:LogBufferBK}\index{BackendKind!LogBufferBK}
\label{code:MonitoringBK}\index{BackendKind!MonitoringBK}
\label{code:SwitchboardBK}\index{BackendKind!SwitchboardBK}
\label{code:TraceAcceptorBK}\index{BackendKind!TraceAcceptorBK}
\label{code:TraceForwarderBK}\index{BackendKind!TraceForwarderBK}
\label{code:UserDefinedBK}\index{BackendKind!UserDefinedBK}
This identifies the backends that can be attached to the |Switchboard|.
\begin{code}

data BackendKind =
      AggregationBK
    | EditorBK
    | EKGViewBK
    | GraylogBK
    | KatipBK
    | LogBufferBK
    | MonitoringBK
    | TraceAcceptorBK
    | TraceForwarderBK
    | UserDefinedBK Text
    | SwitchboardBK
    deriving (Eq, Ord, Show, Read)

instance ToJSON BackendKind where
    toJSON AggregationBK          = String "AggregationBK"
    toJSON EditorBK               = String "EditorBK"
    toJSON EKGViewBK              = String "EKGViewBK"
    toJSON GraylogBK              = String "GraylogBK"
    toJSON KatipBK                = String "KatipBK"
    toJSON LogBufferBK            = String "LogBufferBK"
    toJSON MonitoringBK           = String "MonitoringBK"
    toJSON TraceForwarderBK       = String "TraceForwarderBK"
    toJSON TraceAcceptorBK        = String "TraceAcceptorBK"
    toJSON (UserDefinedBK name)   = object [ "kind" .= String "UserDefinedBK"
                                           , "name" .= toJSON name
                                           ]
    toJSON SwitchboardBK          = String "SwitchboardBK"

instance FromJSON BackendKind where
    parseJSON v = withObject
                    "BackendKind"
                    (\value -> do
                                c <- value .: "kind" :: Parser Text
                                case c of
                                    "UserDefinedBK"   ->
                                        UserDefinedBK <$> value .: "name"
                                    _                 -> fail "not expected kind"
                    )
                    v
              <|> withText
                    "BackendKind"
                    (\case
                        "AggregationBK"    -> pure AggregationBK
                        "EditorBK"         -> pure EditorBK
                        "EKGViewBK"        -> pure EKGViewBK
                        "GraylogBK"        -> pure GraylogBK
                        "KatipBK"          -> pure KatipBK
                        "LogBufferBK"      -> pure LogBufferBK
                        "MonitoringBK"     -> pure MonitoringBK
                        "TraceAcceptorBK"  -> pure TraceAcceptorBK
                        "TraceForwarderBK" -> pure TraceForwarderBK
                        "SwitchboardBK"    -> pure SwitchboardBK
                        _                  -> fail "not expected BackendKind"
                    )
                    v

\end{code}
