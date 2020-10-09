{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedLists   #-}
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
import           Control.Monad.Except            (ExceptT (ExceptT))
import           Control.Monad.Freer             (Eff, Member, type (~>), interpret, runM)
import           Control.Monad.Freer.Extra.Log   (LogMsg, logInfo)
import           Control.Monad.Freer.Log         (handleLogTrace)
import           Control.Monad.IO.Class          (liftIO)
import           Data.Aeson                      ((.=))
import qualified Data.Aeson                      as JSON
import           Data.ByteString                 (ByteString)
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
import           Servant                         (Application, Handler (Handler), hoistServer, serve)
import           Servant.API                     ((:<|>) ((:<|>)))
import           Servant.Client                  (baseUrlPort)
import           Wallet.Emulator.Wallet          (Wallet (Wallet), walletPrivKey, walletPubKey)

fetchSubject :: Subject -> Maybe (SubjectProperties 'AesonEncoding)
fetchSubject subject =
    SubjectProperties subject <$> Map.lookup subject testDatabase

fetchById ::
       Subject -> PropertyKey -> Maybe (Property 'AesonEncoding)
fetchById subject propertyKey = do
    (SubjectProperties _ properties) <- fetchSubject subject
    find (\v -> toPropertyKey v == propertyKey) properties

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
testDatabase :: Map Subject [Property 'AesonEncoding]
testDatabase =
    [ ( toSubject script1
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
    foldMap propertiesForWalletId ([1 .. 10] :: [Integer])
  where
    propertiesForWalletId ::
           Integer -> Map Subject [Property 'AesonEncoding]
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
        GetProperties subject -> do
            logInfo $ FetchingSubject subject
            pure $ fetchSubject subject
        GetProperty subject propertyKey -> do
            logInfo $ FetchingProperty subject propertyKey
            pure $ fetchById subject propertyKey

------------------------------------------------------------
handler ::
       Member MetadataEffect effs
    => Subject
    -> Eff effs (Maybe (SubjectProperties 'AesonEncoding))
       :<|> (PropertyKey -> Eff effs (Maybe (Property 'AesonEncoding)))
handler subject = getProperties subject :<|> getProperty subject

asHandler ::
       Eff '[ MetadataEffect, LogMsg MetadataLogMessage, IO] a -> Handler a
asHandler =
    Handler . ExceptT . fmap Right . runM . handleLogTrace . handleMetadata

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
