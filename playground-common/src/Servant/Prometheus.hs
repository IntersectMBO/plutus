{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Servant.Prometheus (
    HasEndpoint(..),
    APIEndpoint(..),
    monitorEndpoints
) where

import           Control.Exception                              (bracket, bracket_)
import           Control.Monad                                  (mplus)
import           Control.Monad.IO.Class                         (MonadIO)
import           Control.Monad.Logger                           (MonadLogger, MonadLoggerIO)
import qualified Data.HashMap.Strict                            as H
import           Data.Hashable                                  (Hashable)
import           Data.Kind                                      (Type)
import           Data.Proxy                                     (Proxy (Proxy))
import           Data.Text                                      (Text)
import qualified Data.Text                                      as T
import qualified Data.Text.Encoding                             as T
import           Data.Time.Clock                                (diffUTCTime, getCurrentTime)
import           GHC.Generics                                   (Generic)
import           GHC.TypeLits                                   (KnownSymbol, Symbol, symbolVal)
import           Network.HTTP.Types                             (Method, Status (Status, statusCode))
import           Network.Wai                                    (Middleware, Request, pathInfo, requestMethod,
                                                                 responseStatus)
import           Servant.API                                    (BasicAuth, Capture', CaptureAll, Description, EmptyAPI,
                                                                 Header', HttpVersion, IsSecure, QueryFlag, QueryParam',
                                                                 QueryParams, Raw, ReflectMethod, RemoteHost, ReqBody',
                                                                 Stream, Summary, Vault, Verb, WithNamedContext,
                                                                 reflectMethod, (:<|>), (:>))
#if MIN_VERSION_servant(0,15,0)
import           Servant.API                                    (StreamBody')
#endif
import           Servant.API.BrowserHeader                      (BrowserHeader)
import           Servant.API.WebSocket                          (WebSocket, WebSocketPending)
import           System.Metrics.Prometheus.Concurrent.RegistryT (RegistryT, registerCounter, registerGauge,
                                                                 registerHistogram)
import qualified System.Metrics.Prometheus.Metric.Counter       as Counter
import qualified System.Metrics.Prometheus.Metric.Gauge         as Gauge
import qualified System.Metrics.Prometheus.Metric.Histogram     as Histogram
import qualified System.Metrics.Prometheus.MetricId             as MetricId

instance MonadLogger m => MonadLogger (RegistryT m)
instance MonadLoggerIO m => MonadLoggerIO (RegistryT m)

data APIEndpoint = APIEndpoint {
    pathSegments :: [Text],
    method       :: Method
} deriving (Eq, Hashable, Show, Generic)

data Meters = Meters
    { metersInflight :: Gauge.Gauge
    , metersC2XX     :: Counter.Counter
    , metersC4XX     :: Counter.Counter
    , metersC5XX     :: Counter.Counter
    , metersCXXX     :: Counter.Counter
    , metersTime     :: Histogram.Histogram
    }

gaugeInflight :: Gauge.Gauge -> Middleware
gaugeInflight inflight application request respond =
    bracket_ (Gauge.inc inflight)
             (Gauge.dec inflight)
             (application request respond)

-- | Count responses with 2XX, 4XX, 5XX, and XXX response codes.
countResponseCodes
    :: (Counter.Counter, Counter.Counter, Counter.Counter, Counter.Counter)
    -> Middleware
countResponseCodes (c2XX, c4XX, c5XX, cXXX) application request respond =
    application request respond'
  where
    respond' res = count (responseStatus res) >> respond res
    count Status{statusCode = sc }
        | 200 <= sc && sc < 300 = Counter.inc c2XX
        | 400 <= sc && sc < 500 = Counter.inc c4XX
        | 500 <= sc && sc < 600 = Counter.inc c5XX
        | otherwise             = Counter.inc cXXX

responseTimeHistogram :: Histogram.Histogram -> Middleware
responseTimeHistogram hist application request respond =
    bracket getCurrentTime stop $ const $ application request respond
  where
    stop t1 = do
        t2 <- getCurrentTime
        let dt = diffUTCTime t2 t1
        Histogram.observe (fromRational $ (*1000) $ toRational dt) hist

initializeMeters :: MonadIO m => APIEndpoint -> RegistryT m Meters
initializeMeters APIEndpoint{..} = do
    metersInflight <- registerGauge        (prefix <> "in_flight") mempty
    metersC2XX     <- registerCounter      (prefix <> "responses_2XX") mempty
    metersC4XX     <- registerCounter      (prefix <> "responses_4XX") mempty
    metersC5XX     <- registerCounter      (prefix <> "responses_5XX") mempty
    metersCXXX     <- registerCounter      (prefix <> "responses_XXX") mempty
    metersTime     <- registerHistogram (prefix <> "time_ms") mempty [10,20..100]
    pure Meters{..}
    where
        prefix = MetricId.Name . T.toLower $ "servant_path_" <> path <> "_"
        path   = T.intercalate "_" $ pathSegments <> [T.decodeUtf8 method]

initializeMetersTable :: MonadIO m => [APIEndpoint] -> RegistryT m (H.HashMap APIEndpoint Meters)
initializeMetersTable endpoints = do
    meters <- mapM initializeMeters endpoints
    pure $ H.fromList (zip endpoints meters)

monitorEndpoints ::
       (MonadIO m, HasEndpoint api) => Proxy api -> RegistryT m Middleware
monitorEndpoints proxy = do
    meters <- initializeMetersTable (enumerateEndpoints proxy)
    return (monitorEndpointsWith meters)
  where
    monitorEndpointsWith :: H.HashMap APIEndpoint Meters -> Middleware
    monitorEndpointsWith meters application request respond =
        case getEndpoint proxy request >>= \ep -> H.lookup ep meters of
            Nothing -> application request respond
            Just endpointMeter ->
                updateCounters endpointMeter application request respond
      where
        updateCounters Meters {..} =
            responseTimeHistogram metersTime .
            countResponseCodes (metersC2XX, metersC4XX, metersC5XX, metersCXXX) .
            gaugeInflight metersInflight


class HasEndpoint a where
    getEndpoint        :: Proxy a -> Request -> Maybe APIEndpoint
    enumerateEndpoints :: Proxy a -> [APIEndpoint]

instance HasEndpoint EmptyAPI where
    getEndpoint      _ _ = Nothing
    enumerateEndpoints _ = []

instance (HasEndpoint (a :: Type), HasEndpoint (b :: Type)) => HasEndpoint (a :<|> b) where
    getEndpoint _ req =
                getEndpoint (Proxy :: Proxy a) req
        `mplus` getEndpoint (Proxy :: Proxy b) req

    enumerateEndpoints _ =
           enumerateEndpoints (Proxy :: Proxy a)
        <> enumerateEndpoints (Proxy :: Proxy b)

instance (KnownSymbol (path :: Symbol), HasEndpoint (sub :: Type))
    => HasEndpoint (path :> sub) where
    getEndpoint _ req =
        case pathInfo req of
            p:ps | p == T.pack (symbolVal (Proxy :: Proxy path)) -> do
                APIEndpoint{..} <- getEndpoint (Proxy :: Proxy sub) req{ pathInfo = ps }
                return (APIEndpoint (p:pathSegments) method)
            _ -> Nothing

    enumerateEndpoints _ =
        let endpoints               = enumerateEndpoints (Proxy :: Proxy sub)
            currentSegment          = T.pack $ symbolVal (Proxy :: Proxy path)
            qualify APIEndpoint{..} = APIEndpoint (currentSegment : pathSegments) method
        in
            map qualify endpoints

instance (KnownSymbol (capture :: Symbol), HasEndpoint (sub :: Type))
    => HasEndpoint (Capture' mods capture a :> sub) where
    getEndpoint _ req =
        case pathInfo req of
            _:ps -> do
                APIEndpoint{..} <- getEndpoint (Proxy :: Proxy sub) req{ pathInfo = ps }
                let p = T.pack $ (':':) $ symbolVal (Proxy :: Proxy capture)
                return (APIEndpoint (p:pathSegments) method)
            _ -> Nothing
    enumerateEndpoints _ =
        let endpoints               = enumerateEndpoints (Proxy :: Proxy sub)
            currentSegment          = T.pack $ (':':) $ symbolVal (Proxy :: Proxy capture)
            qualify APIEndpoint{..} = APIEndpoint (currentSegment : pathSegments) method
        in
            map qualify endpoints

instance HasEndpoint (sub :: Type) => HasEndpoint (Summary d :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (Description d :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (Header' mods h a :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (QueryParam' mods (h :: Symbol) a :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (QueryParams (h :: Symbol) a :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (QueryFlag h :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (ReqBody' mods cts a :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

#if MIN_VERSION_servant(0,15,0)
instance HasEndpoint (sub :: Type) => HasEndpoint (StreamBody' mods framing ct a :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)
#endif

instance HasEndpoint (sub :: Type) => HasEndpoint (RemoteHost :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (IsSecure :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (HttpVersion :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (Vault :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (WithNamedContext x y sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance ReflectMethod method => HasEndpoint (Verb method status cts a) where
    getEndpoint _ req = case pathInfo req of
        [] | requestMethod req == method -> Just (APIEndpoint [] method)
        _                                -> Nothing
      where method = reflectMethod (Proxy :: Proxy method)

    enumerateEndpoints _ = [APIEndpoint mempty method]
      where method = reflectMethod (Proxy :: Proxy method)

instance ReflectMethod method => HasEndpoint (Stream method status framing ct a) where
    getEndpoint _ req = case pathInfo req of
        [] | requestMethod req == method -> Just (APIEndpoint [] method)
        _                                -> Nothing
      where method = reflectMethod (Proxy :: Proxy method)

    enumerateEndpoints _ = [APIEndpoint mempty method]
      where method = reflectMethod (Proxy :: Proxy method)

instance HasEndpoint Raw where
    getEndpoint      _ _ = Just (APIEndpoint [] "RAW")
    enumerateEndpoints _ =      [APIEndpoint [] "RAW"]

instance HasEndpoint WebSocketPending where
    getEndpoint      _ _ = Just (APIEndpoint [] "Websocket")
    enumerateEndpoints _ =      [APIEndpoint [] "Websocket"]

instance HasEndpoint WebSocket where
    getEndpoint      _ _ = Just (APIEndpoint [] "Websocket")
    enumerateEndpoints _ =      [APIEndpoint [] "Websocket"]

instance HasEndpoint (sub :: Type) => HasEndpoint (CaptureAll (h :: Symbol) a :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (sub :: Type) => HasEndpoint (BasicAuth (realm :: Symbol) a :> sub) where
    getEndpoint        _ = getEndpoint        (Proxy :: Proxy sub)
    enumerateEndpoints _ = enumerateEndpoints (Proxy :: Proxy sub)

instance HasEndpoint (BrowserHeader "Cookie" Text :> a) where
  getEndpoint      _ _ = Nothing
  enumerateEndpoints _ = []
