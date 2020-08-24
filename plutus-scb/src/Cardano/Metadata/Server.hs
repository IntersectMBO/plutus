{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Metadata.Server
    ( main
    ) where

import           Cardano.Metadata.API            (API)
import           Cardano.Metadata.Types          (AnnotatedSignature (AnnotatedSignature), HashFunction (SHA256),
                                                  MetadataConfig (MetadataConfig), Property (Property),
                                                  PropertyDescription (Name, Other, Preimage), PropertyKey,
                                                  Subject (Subject), mdBaseUrl, toId, toPayload, _propertyDescription,
                                                  _propertySubject)
import           Control.Concurrent.Availability (Availability, available)
import           Control.Monad.Except            (ExceptT, throwError)
import           Control.Monad.Freer.Extra.Log   (logInfo)
import           Control.Monad.IO.Class          (liftIO)
import           Crypto.Hash                     (Digest, SHA256, hashlazy)
import           Data.Aeson                      ((.=))
import qualified Data.Aeson                      as JSON
import           Data.ByteString                 (ByteString)
import           Data.Function                   ((&))
import           Data.List                       (find)
import           Data.List.NonEmpty              (NonEmpty ((:|)))
import           Data.Proxy                      (Proxy (Proxy))
import qualified Data.Text                       as Text
import           Data.Text.Encoding              (encodeUtf8)
import           Ledger.Crypto                   (PrivateKey, PubKey, getPubKey, sign)
import           LedgerBytes                     (LedgerBytes)
import qualified LedgerBytes
import qualified Network.Wai.Handler.Warp        as Warp
import           Plutus.SCB.App                  (App)
import           Plutus.SCB.SCBLogMsg            (ContractExeLogMsg (StartingMetadataServer))
import           Plutus.SCB.Utils                (tshow)
import           Servant                         (Application, Handler (Handler), ServerError, err404, errBody,
                                                  hoistServer, serve)
import           Servant.API                     ((:<|>) ((:<|>)))
import           Servant.Client                  (baseUrlPort)
import           Wallet.Emulator.Wallet          (Wallet (Wallet), walletPrivKey, walletPubKey)

fetchSubject :: Subject -> ExceptT ServerError IO [Property]
fetchSubject subject =
    pure $ filter (\v -> _propertySubject v == subject) testDatabase

fetchById :: Subject -> PropertyKey -> ExceptT ServerError IO JSON.Value
fetchById subject propertyKey =
    case find (\v -> toId v == (subject, propertyKey)) testDatabase of
        Nothing     -> throwError $ err404 {errBody = "Not Found"}
        Just result -> pure $ toPayload $ _propertyDescription result

handler ::
       Subject
    -> (ExceptT ServerError IO [Property]
        :<|> (PropertyKey -> ExceptT ServerError IO JSON.Value))
handler subject = fetchSubject subject :<|> fetchById subject

asHandler :: ExceptT ServerError IO a -> Handler a
asHandler = Handler

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
        , Property
              (toSubject (getPubKey pubKey1))
              (Preimage SHA256 (getPubKey pubKey1))
        , Property
              (toSubject (getPubKey pubKey1))
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
        ((\index ->
              let wallet = Wallet index
                  public = walletPubKey wallet
                  private = walletPrivKey wallet
                  name = ("Wallet #" <> tshow index)
               in Property
                      (toSubject (getPubKey public))
                      (Name
                           name
                           (AnnotatedSignature
                                public
                                (sign (encodeUtf8 name) private) :|
                            []))) <$>
         [1 .. 10])

    where
        toSubject :: LedgerBytes -> Subject
        toSubject x =
            Subject
                (Text.pack
                     (show (hashlazy (LedgerBytes.bytes x) :: Digest SHA256)))
