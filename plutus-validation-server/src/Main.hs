{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Codec.Serialise             as CBOR
import           Data.Aeson
import qualified Data.ByteString             as BS
import           Data.ByteString.Base64.Type (getByteString64)
import qualified Data.ByteString.Base64.Type as BS64
import qualified Data.ByteString.Lazy        as BSL
import           GHC.Generics                (Generic)
import           Ledger                      (DataScript (..), RedeemerScript (..), Script, ValidationData (..),
                                              ValidatorScript (..), runScript)
import           Network.HTTP.Types.Status
import           Network.Wai
import           Network.Wai.Handler.Warp

main :: IO ()
main = run 3000 app

trueJSON :: BSL.ByteString
trueJSON = "{\"isValid\":true}"

falseJSON :: BSL.ByteString
falseJSON = "{\"isValid\":false}"

-- includes: slot, inputs, outputs, input/output pair currently being validated
-- fee, value forged by transation
--
-- I should ask Vincent what he wants to/is able to provide (look at checkMatch)

-- TODO: encoding: base16 or base64? Ask Vincent
-- If base16 we probably want to use the module in wallet-api
data ToValidate = ToValidate { validationData :: BS64.ByteString64
                             , validator      :: BS64.ByteString64
                             , redeemer       :: BS64.ByteString64
                             , dataScript     :: BS64.ByteString64
                             } deriving (Generic, FromJSON)

getScript :: BS.ByteString -> Either CBOR.DeserialiseFailure Script
getScript bs = CBOR.deserialiseOrFail (BSL.fromStrict bs)

-- TODO: make a curl request to test this (also look at automated tests already
-- there)
-- TODO: at least deserialize from a valid script (and then test it)
-- TODO: should we have a separate way to query run logs?
validateByteString :: BS.ByteString -- ^ Validation Data
                   -> BS.ByteString -- ^ Validator script
                   -> BS.ByteString -- ^ Data script
                   -> BS.ByteString -- ^ Redeemer script
                   -> Either CBOR.DeserialiseFailure Bool
validateByteString vd vs d r =
    fmap snd $ runScript
        <$> (ValidationData <$> getScript vd)
        <*> (ValidatorScript <$> getScript vs)
        <*> (DataScript <$> getScript d)
        <*> (RedeemerScript <$> getScript r)

validateResponse :: ToValidate -> (Status, BSL.ByteString)
validateResponse (ToValidate vd v r d) =
    case validateByteString (getByteString64 vd) (getByteString64 v) (getByteString64 d) (getByteString64 r) of
        Left{}        -> (status400, mempty)
        (Right True)  -> (status200, trueJSON)
        (Right False) -> (status200, falseJSON)

-- typecheck, run/validate
app :: Application
app req respond = do
    bsReq <- lazyRequestBody req
    -- TODO: check that it's a GET method
    let decoded = decode bsReq
        validated = fmap validateResponse decoded
        (stat, resp) = case validated of
            Just x  -> x
            Nothing -> (status400, mempty)
    respond $ responseLBS stat [] resp
