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
import           Control.Monad.Freer             (Eff, Member, interpret, runM)
import           Control.Monad.Freer.Error       (Error, runError, throwError)
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
import           Data.Proxy                      (Proxy (Proxy))
import           Data.Text.Encoding              (encodeUtf8)
import           Ledger.Crypto                   (PrivateKey, PubKey, getPubKey, pubKeyHash, sign)
import           LedgerBytes                     (LedgerBytes)
import qualified Network.Wai.Handler.Warp        as Warp
import           Plutus.SCB.App                  (App)
import           Plutus.SCB.SCBLogMsg            (ContractExeLogMsg (StartingMetadataServer))
import           Plutus.SCB.Utils                (tshow)
import           Servant                         (Application, Handler (Handler), ServerError, err404, errBody,
                                                  hoistServer, serve)
import           Servant.API                     ((:<|>) ((:<|>)))
import           Servant.Client                  (baseUrlPort)
import           Wallet.Emulator.Wallet          (Wallet (Wallet), walletPrivKey, walletPubKey)

toServerError :: MetadataError -> ServerError
toServerError (SubjectNotFound subject) =
    err404 {errBody = BSL8.pack $ "Subject not found: " <> show subject}
toServerError (PropertyNotFound subject propertyKey) =
    err404
        { errBody =
              BSL8.pack $
              "Property not found: " <> show subject <> ", " <> show propertyKey
        }

fetchSubject ::
       ( Member (LogMsg MetadataLogMessage) effs
       , Member (Error MetadataError) effs
       )
    => Subject
    -> Eff effs [Property]
fetchSubject subject = do
    logInfo $ FetchingSubject subject
    let matches = filter (\v -> _propertySubject v == subject) testDatabase
    case matches of
        [] -> throwError $ SubjectNotFound subject
        _  -> pure matches

fetchById ::
       ( Member (LogMsg MetadataLogMessage) effs
       , Member (Error MetadataError) effs
       )
    => Subject
    -> PropertyKey
    -> Eff effs Property
fetchById subject propertyKey = do
    logInfo $ FetchingProperty subject propertyKey
    let match = find (\v -> toId v == (subject, propertyKey)) testDatabase
    case match of
        Nothing     -> throwError $ PropertyNotFound subject propertyKey
        Just result -> pure result

handler ::
       ( Member (LogMsg MetadataLogMessage) effs
       , Member (Error MetadataError) effs
       )
    => Subject
    -> Eff effs [Property]
       :<|> (PropertyKey -> Eff effs Property)
handler subject = fetchSubject subject :<|> fetchById subject

asHandler ::
       Eff '[ LogMsg MetadataLogMessage, Error MetadataError, IO] a -> Handler a
asHandler =
    Handler .
    withExceptT toServerError . ExceptT . runM . runError . handleLogTrace

app :: Application
app = serve api apiServer
  where
    api = Proxy @API
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

annotatedSignature1, annotatedSignature2 :: AnnotatedSignature
(annotatedSignature1, annotatedSignature2) =
    ( AnnotatedSignature pubKey1 (sign ("TEST 1" :: ByteString) privateKey1)
    , AnnotatedSignature pubKey2 (sign ("TEST 2" :: ByteString) privateKey2))

script1 :: LedgerBytes
script1 = "0001abc1"

-- | The test database contains a mix of example properties from the
-- | spec document, and mock wallet details.
testDatabase :: [Property]
testDatabase =
    [ Property (toSubject script1) (Preimage SHA256 script1)
    , Property
          (toSubject script1)
          (Name "Fred's Script" (annotatedSignature1 :| []))
    , Property (toSubject pubKey1) (Preimage SHA256 (getPubKey pubKey1))
    , Property
          (toSubject pubKey1)
          (Name "Fred's Key" (annotatedSignature1 :| [annotatedSignature2]))
    , Property
          (Subject "UTXO 0001")
          (Other
               "Exchange Offer"
               (JSON.object
                    [ "fromCur" .= JSON.String "Ada"
                    , "fromAmount" .= JSON.Number 5
                    , "toCur" .= JSON.String "FredTokens"
                    , "toAmount" .= JSON.Number 20
                    ])
               (annotatedSignature1 :| []))
    , Property
          (Subject "gold_price_usd")
          (Other
               "on-chain location"
               (JSON.String "UTXO 0002")
               (annotatedSignature1 :| []))
    ] <>
    foldMap propertiesForWalletId [1 .. 10]
  where
    propertiesForWalletId :: Integer -> [Property]
    propertiesForWalletId index =
        let name = ("Wallet #" <> tshow index)
            wallet = Wallet index
            public = walletPubKey wallet
            private = walletPrivKey wallet
            publicHash = pubKeyHash public
            signatures =
                AnnotatedSignature public (sign (encodeUtf8 name) private) :| []
         in [ Property (toSubject public) (Name name signatures)
            , Property (toSubject publicHash) (Name name signatures)
            ]

handleMetadata ::
       forall effs a.
       ( Member (LogMsg MetadataLogMessage) effs
       , Member (Error MetadataError) effs
       )
    => Eff (MetadataEffect ': effs) a
    -> Eff effs a
handleMetadata =
    interpret $ \case
        GetProperties subject -> fetchSubject subject
        GetProperty subject propertyKey -> fetchById subject propertyKey
