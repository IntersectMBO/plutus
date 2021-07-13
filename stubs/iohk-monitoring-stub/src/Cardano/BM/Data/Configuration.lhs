
\subsection{Cardano.BM.Data.Configuration}
\label{code:Cardano.BM.Data.Configuration}

Data structure to help parsing configuration files.

%if style == newcode
\begin{code}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards     #-}

module Cardano.BM.Data.Configuration
  (
    Representation (..)
  , Port
  , HostPort
  , Endpoint (..)
  , RemoteAddr (..)
  , RemoteAddrNamed (..)
  , parseRepresentation
  , readRepresentation
  )
  where

import           Control.Exception (throwIO)
import           Data.Aeson.Types (genericParseJSON, defaultOptions, typeMismatch)
import           Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as BS
import qualified Data.HashMap.Strict as HM
import           Data.Text (Text, unpack)
import qualified Data.Set as Set
import           Data.Scientific (Scientific, toBoundedInteger)
import qualified Data.Vector as V
import           Data.Yaml
import           GHC.Generics

import           Cardano.BM.Data.BackendKind
import           Cardano.BM.Data.Output
import           Cardano.BM.Data.Severity
import           Cardano.BM.Data.Rotation

\end{code}
%endif

\subsubsection{Representation}\label{code:Representation}\index{Representation}\label{code:Port}\index{Port}
\begin{code}
type Port = Int
type HostPort = (String, Port)
newtype Endpoint = Endpoint HostPort
  deriving (Eq, Generic, Show, ToJSON)

-- It's possible to specify host and port for EKG or port only
-- (to keep backward compatibility with existing configurations).
-- For example:
--   hasEKG:
--     - "127.0.0.1"
--     - 12789
-- or
--   hasEKG: 12789
-- That's why we provide a custom FromJSON-instance for Endpoint.
instance FromJSON Endpoint where
  parseJSON o@(Array a) =
    case V.toList a of
      [h, p] -> do
        host <-
          case h of
            String s -> return s
            _ -> typeMismatch "String" h
        port <-
          case p of
            Number n ->
              case mkInt n of
                Just p' -> return p'
                Nothing -> typeMismatch "Number" p
            _ -> typeMismatch "Object" p
        return $ Endpoint (unpack host, port)
      _ -> typeMismatch "Array" o

  parseJSON o@(Number n) =
    case mkInt n of
      Just port -> return $ Endpoint ("127.0.0.1", port)
      Nothing -> typeMismatch "Number" o

  parseJSON invalid =
    typeMismatch "Object" invalid

mkInt :: Scientific -> Maybe Int
mkInt = toBoundedInteger

data Representation = Representation
    { minSeverity     :: Severity
    , rotation        :: Maybe RotationParameters
    , setupScribes    :: [ScribeDefinition]
    , defaultScribes  :: [(ScribeKind,Text)]
    , setupBackends   :: [BackendKind]
    , defaultBackends :: [BackendKind]
    , hasEKG          :: Maybe Endpoint
    , hasGraylog      :: Maybe Port
    , hasPrometheus   :: Maybe HostPort
    , hasGUI          :: Maybe Port
    , traceForwardTo  :: Maybe RemoteAddr
    , forwardDelay    :: Maybe Word
    , traceAcceptAt   :: Maybe [RemoteAddrNamed]
    , options         :: HM.HashMap Text Value
    }
    deriving (Eq, Generic, Show, ToJSON)

instance FromJSON Representation where
  parseJSON value = implicit_fill_representation <$> genericParseJSON defaultOptions value

data RemoteAddr
  = RemotePipe FilePath
  | RemoteSocket String String
  deriving (Generic, Eq, Show, ToJSON, FromJSON)

data RemoteAddrNamed = RemoteAddrNamed
  { nodeName   :: Text
  , remoteAddr :: RemoteAddr
  } deriving (Generic, Eq, Show, ToJSON, FromJSON)

\end{code}

\subsubsection{readRepresentation}\label{code:readRepresentation}\index{readRepresentation}
\begin{code}
readRepresentation :: FilePath -> IO Representation
readRepresentation fp =
    either throwIO pure =<< decodeEither' <$> BS.readFile fp

\end{code}

\subsubsection{parseRepresentation}\label{code:parseRepresentation}\index{parseRepresentation}
\begin{code}
{-# DEPRECATED parseRepresentation "Use decodeEither' instead" #-}
parseRepresentation :: ByteString -> Either ParseException Representation
parseRepresentation = decodeEither'

\end{code}


after parsing the configuration representation we implicitly correct it.
\begin{code}
implicit_fill_representation :: Representation -> Representation
implicit_fill_representation =
    remove_ekgview_if_not_defined .
    filter_duplicates_from_backends .
    filter_duplicates_from_scribes .
    union_setup_and_usage_backends .
    add_ekgview_if_port_defined .
    add_katip_if_any_scribes
  where
    filter_duplicates_from_backends r =
        r {setupBackends = mkUniq $ setupBackends r}
    filter_duplicates_from_scribes r =
        r {setupScribes = mkUniq $ setupScribes r}
    union_setup_and_usage_backends r =
        r {setupBackends = setupBackends r <> defaultBackends r}
    remove_ekgview_if_not_defined r =
        case hasEKG r of
        Nothing -> r { defaultBackends = filter (\bk -> bk /= EKGViewBK) (defaultBackends r)
                     , setupBackends = filter (\bk -> bk /= EKGViewBK) (setupBackends r)
                     }
        Just _  -> r
    add_ekgview_if_port_defined r =
        case hasEKG r of
        Nothing -> r
        Just _  -> r {setupBackends = setupBackends r <> [EKGViewBK]}
    add_katip_if_any_scribes r =
        if (any not [null $ setupScribes r, null $ defaultScribes r])
        then r {setupBackends = setupBackends r <> [KatipBK]}
        else r
    mkUniq :: Ord a => [a] -> [a]
    mkUniq = Set.toList . Set.fromList

\end{code}
