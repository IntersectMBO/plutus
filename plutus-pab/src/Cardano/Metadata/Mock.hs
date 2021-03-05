{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Metadata.Mock
    ( handleMetadata
     -- * required by tests
    , script1
    , annotatedSignature1
    ) where

import           Cardano.Metadata.Types
import           Control.Monad.Freer            (Eff, Member, interpret, type (~>))
import           Control.Monad.Freer.Error      (Error, throwError)
import           Control.Monad.Freer.Extras.Log (LogMsg, logDebug)
import           Data.Aeson                     ((.=))
import qualified Data.Aeson                     as JSON
import           Data.ByteString                (ByteString)
import           Data.List                      (find)
import           Data.List.NonEmpty             (NonEmpty ((:|)))
import           Data.Map                       (Map)
import qualified Data.Map                       as Map
import           Data.Maybe                     (fromMaybe)
import           Data.Set                       (Set)
import qualified Data.Set                       as Set
import           Data.Text.Encoding             (encodeUtf8)
import           Data.Text.Extras               (tshow)
import           Ledger.Bytes                   (LedgerBytes)
import           Ledger.Crypto                  (PrivateKey, PubKey, getPubKey, pubKeyHash, sign)
import           Wallet.Emulator.Wallet         (Wallet (Wallet), walletPrivKey, walletPubKey)



fetchSubject :: Subject -> Maybe (SubjectProperties 'AesonEncoding)
fetchSubject subject =
    SubjectProperties subject <$> Map.lookup subject testDatabase

fetchById :: Subject -> PropertyKey -> Maybe (Property 'AesonEncoding)
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
    propertiesForWalletId :: Integer -> Map Subject [Property 'AesonEncoding]
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
       ( Member (LogMsg MetadataLogMessage) effs
       , Member (Error MetadataError) effs
       )
    => Eff (MetadataEffect ': effs) ~> Eff effs
handleMetadata =
    interpret $ \case
        GetProperties subject -> do
            logDebug $ FetchingSubject subject
            case fetchSubject subject of
                Nothing     -> throwError $ SubjectNotFound subject
                Just result -> pure result
        GetProperty subject propertyKey -> do
            logDebug $ FetchingProperty subject propertyKey
            case fetchById subject propertyKey of
                Nothing ->
                    throwError $ SubjectPropertyNotFound subject propertyKey
                Just result -> pure result
        BatchQuery query@QuerySubjects {subjects, propertyNames} -> do
            logDebug $ Querying query
            pure .
                QueryResult .
                fmap (filterSubjectProperties propertyNames) .
                fromMaybe [] . traverse fetchSubject $
                Set.toList subjects

filterSubjectProperties ::
       Maybe (Set PropertyKey)
    -> SubjectProperties 'AesonEncoding
    -> SubjectProperties 'AesonEncoding
filterSubjectProperties keys (SubjectProperties subject properties) =
    SubjectProperties subject (filterProperties keys properties)

filterProperties ::
       Maybe (Set PropertyKey)
    -> [Property 'AesonEncoding]
    -> [Property 'AesonEncoding]
filterProperties Nothing properties = properties
filterProperties (Just keys) properties =
    filter (\property -> Set.member (toPropertyKey property) keys) properties
