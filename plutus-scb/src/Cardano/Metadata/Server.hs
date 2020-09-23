{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}

{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Metadata.Server
    ( main
    , fetchSubject
    , fetchById
    , handleMetadata
    ) where

import           Cardano.Metadata.API            (API)
import           Cardano.Metadata.Types
import           Control.Concurrent.Availability (Availability, available)
import           Control.Monad.Except            (ExceptT (ExceptT), withExceptT)
import           Control.Monad.Freer             (Eff, Member, type (~>), interpret, runM)
import           Control.Monad.Freer.Error       (Error, runError)
import           Control.Monad.Freer.Extra.Log   (LogMsg, logInfo)
import           Control.Monad.Freer.Log         (handleLogTrace)
import           Control.Monad.IO.Class          (liftIO)
import           Data.Aeson                      ((.=))
import qualified Data.Aeson                      as JSON
import           Data.ByteString                 (ByteString)
import qualified Data.ByteString.Lazy.Char8      as BSL8
import           Data.Function                   ((&))
import           Data.List                       (find)
import           Data.List.NonEmpty              (NonEmpty ((:|)))
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import           Data.Proxy                      (Proxy (Proxy))
import           Data.Text.Encoding              (encodeUtf8)
import           Ledger.Crypto                   (PrivateKey, PubKey, getPubKey, pubKeyHash, sign)
import           LedgerBytes                     (LedgerBytes)
import qualified Network.Wai.Handler.Warp        as Warp
import           Plutus.SCB.App                  (App)
import           Plutus.SCB.SCBLogMsg            (ContractExeLogMsg (StartingMetadataServer))
import           Plutus.SCB.Utils                (tshow)
import           Servant                         (Application, Handler (Handler), ServerError, err500, errBody,
                                                  hoistServer, serve)
import           Servant.API                     ((:<|>) ((:<|>)))
import           Servant.Client                  (baseUrlPort)
import           Wallet.Emulator.Wallet          (Wallet (Wallet), walletPrivKey, walletPubKey)

toServerError :: MetadataError -> ServerError
toServerError (MetadataClientError err) =
    err500
        { errBody =
              BSL8.fromStrict . encodeUtf8 $
              "Error contacting metadata server: " <> tshow err
        }

fetchSubject ::
       Member (LogMsg MetadataLogMessage) effs
    => Subject
    -> Eff effs (Maybe (SubjectProperties 'AesonEncoding))
fetchSubject subject = do
    logInfo $ FetchingSubject subject
    case Map.lookup subject testDatabase of
        Nothing    -> pure Nothing
        Just match -> pure $ Just $ SubjectProperties subject match

fetchById ::
       Member (LogMsg MetadataLogMessage) effs
    => Subject
    -> PropertyKey
    -> Eff effs (Maybe (PropertyDescription 'AesonEncoding))
fetchById subject propertyKey = do
    logInfo $ FetchingProperty subject propertyKey
    result <- fetchSubject subject
    case result of
        Just (SubjectProperties _ properties) ->
            pure $ find (\v -> toPropertyKey v == propertyKey) properties
        Nothing -> pure Nothing

handler ::
       Member (LogMsg MetadataLogMessage) effs
    => Subject
    -> Eff effs (Maybe (SubjectProperties 'AesonEncoding))
       :<|> (PropertyKey -> Eff effs (Maybe (PropertyDescription 'AesonEncoding)))
handler subject = fetchSubject subject :<|> fetchById subject

asHandler ::
       Eff '[ LogMsg MetadataLogMessage, Error MetadataError, IO] a -> Handler a
asHandler =
    Handler .
    withExceptT toServerError . ExceptT . runM . runError . handleLogTrace

app :: Application
app = serve api apiServer
  where
    api = Proxy @(API 'AesonEncoding)
    apiServer = hoistServer api asHandler handler

main :: MetadataConfig -> Availability -> App ()
main MetadataConfig {mdBaseUrl} availability = do
    let port = baseUrlPort mdBaseUrl
        warpSettings :: Warp.Settings
        warpSettings =
            Warp.defaultSettings & Warp.setPort port &
            Warp.setBeforeMainLoop (available availability)
    logInfo $ StartingMetadataServer port
    liftIO $ Warp.runSettings warpSettings app

------------------------------------------------------------
pubKey1, pubKey2 :: PubKey
(pubKey1, pubKey2) = (walletPubKey $ Wallet 1, walletPubKey $ Wallet 2)

privateKey1, privateKey2 :: PrivateKey
(privateKey1, privateKey2) =
    (walletPrivKey $ Wallet 1, walletPrivKey $ Wallet 2)

annotatedSignature1, annotatedSignature2 :: AnnotatedSignature 'AesonEncoding
(annotatedSignature1, annotatedSignature2) =
    ( AnnotatedSignature pubKey1 (sign ("TEST 1" :: ByteString) privateKey1)
    , AnnotatedSignature pubKey2 (sign ("TEST 2" :: ByteString) privateKey2))

script1 :: LedgerBytes
script1 = "0001abc1"

-- | The test database contains a mix of example properties from the
-- | spec document, and mock wallet details.
testDatabase :: Map Subject [PropertyDescription 'AesonEncoding]
testDatabase =
    Map.fromList
        ([ ( toSubject script1
           , [ Preimage SHA256 script1
             , Name "Fred's Script" (annotatedSignature1 :| [])
             ])
         , ( toSubject pubKey1
           , [ Preimage SHA256 (getPubKey pubKey1)
             , Name "Fred's Key" (annotatedSignature1 :| [annotatedSignature2])
             ])
         , ( Subject "UTXO 0001"
           , [ Other
                   "Exchange Offer"
                   (JSON.object
                        [ "fromCur" .= JSON.String "Ada"
                        , "fromAmount" .= JSON.Number 5
                        , "toCur" .= JSON.String "FredTokens"
                        , "toAmount" .= JSON.Number 20
                        ])
                   (annotatedSignature1 :| [])
             ])
         , ( Subject "gold_price_usd"
           , [ Other
                   "on-chain location"
                   (JSON.String "UTXO 0002")
                   (annotatedSignature1 :| [])
             ])
         ] <>
         foldMap propertiesForWalletId [1 .. 10])
  where
    propertiesForWalletId :: Integer -> [(Subject, [PropertyDescription 'AesonEncoding])]
    propertiesForWalletId index =
        let name = ("Wallet #" <> tshow index)
            wallet = Wallet index
            public = walletPubKey wallet
            private = walletPrivKey wallet
            publicHash = pubKeyHash public
            signatures =
                AnnotatedSignature public (sign (encodeUtf8 name) private) :| []
         in [ (toSubject public, [Name name signatures])
            , (toSubject publicHash, [Name name signatures])
            ]

handleMetadata ::
       Member (LogMsg MetadataLogMessage) effs
    => Eff (MetadataEffect ': effs) ~> Eff effs
handleMetadata =
    interpret $ \case
        GetProperties subject -> fetchSubject subject
        GetProperty subject propertyKey -> fetchById subject propertyKey
