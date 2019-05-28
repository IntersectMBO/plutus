{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main, validateBytes) where

import qualified Codec.Serialise             as CBOR
import           Data.Aeson
import qualified Data.ByteString             as BS
import           Data.ByteString.Base64.Type (getByteString64)
import qualified Data.ByteString.Base64.Type as BS64
import qualified Data.ByteString.Lazy        as BSL
import           GHC.Generics                (Generic)
import           Ledger                      (DataScript (..), PendingTx, RedeemerScript (..), Script,
                                              ValidationData (..), ValidatorScript (..), lifted, runScript)
import           Network.HTTP.Types.Status
import           Network.Wai
import           Network.Wai.Handler.Warp

main :: IO ()
main = run 3000 app

trueJSON :: BSL.ByteString
trueJSON = "{\"isValid\":true}"

falseJSON :: BSL.ByteString
falseJSON = "{\"isValid\":false}"

convertPendingTx :: PendingTx -> ValidationData
convertPendingTx = ValidationData . lifted

data ToValidate = ToValidate { validationData :: PendingTx
                             , validator      :: BS64.ByteString64
                             , dataScript     :: BS64.ByteString64
                             , redeemer       :: BS64.ByteString64
                             } deriving (Generic, FromJSON)

getScript :: BS.ByteString -> Either CBOR.DeserialiseFailure Script
getScript = CBOR.deserialiseOrFail . BSL.fromStrict

-- TODO: should we have a separate way to query run logs?
-- Also gas costs at some point...
validateByteString :: PendingTx -- ^ Validation Data
                   -> BS.ByteString -- ^ Validator script
                   -> BS.ByteString -- ^ Redeemer script
                   -> BS.ByteString -- ^ Data script
                   -> Either CBOR.DeserialiseFailure Bool
validateByteString vd vs d r =
    fmap snd $ runScript
            (convertPendingTx vd)
        <$> (ValidatorScript <$> getScript vs)
        <*> (DataScript <$> getScript d)
        <*> (RedeemerScript <$> getScript r)

validateResponse :: ToValidate -> (Status, BSL.ByteString)
validateResponse (ToValidate vd v r d) =
    case validateByteString vd (getByteString64 v) (getByteString64 r) (getByteString64 d) of
        Left{}        -> (status400, mempty)
        (Right True)  -> (status200, trueJSON)
        (Right False) -> (status200, falseJSON)

validateBytes :: BSL.ByteString -> (Status, BSL.ByteString)
validateBytes bs =
    let decoded = decode bs
        validated = fmap validateResponse decoded
    in
    case validated of
        Just x  -> x
        Nothing -> (status400, mempty)

-- typecheck, run/validate
app :: Application
app req respond = do
    bsReq <- lazyRequestBody req
    -- TODO: check that it's a GET method
    -- testing idea: use approach present in plutus-playground-server, i.e. the
    -- approach of only testing pure appratus with JSON but not actual requests.
    -- Also look at Servant
    let (stat, resp) = validateBytes bsReq
    respond $ responseLBS stat [] resp
