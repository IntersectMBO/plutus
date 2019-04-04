{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Data.Aeson
import           Data.Aeson.Types
import qualified Data.ByteString             as BS
import           Data.ByteString.Base64.Type (getByteString64)
import qualified Data.ByteString.Base64.Type as BS64
import qualified Data.ByteString.Lazy        as BSL
import           Network.HTTP.Types.Status
import           Network.Wai
import           Network.Wai.Handler.Warp

main :: IO ()
main = run 3000 app

trueJSON :: BSL.ByteString
trueJSON = "{\"isValid\":true}"

falseJSON :: BSL.ByteString
falseJSON = "{\"isValid\":false}"

-- TODO: encoding: base16 or base64? Ask Vincent
data ToValidate = ToValidate { _validator :: BS64.ByteString64
                             , _redeemer  :: BS64.ByteString64
                             , _data      :: BS64.ByteString64
                             }

instance FromJSON ToValidate where
    parseJSON (Object v) = ToValidate
        <$> v .: "validator"
        <*> v .: "redeemer"
        <*> v .: "data"
    parseJSON invalid    = typeMismatch "ToValidate" invalid

-- TODO: make a curl request to test this
validateByteString :: BS.ByteString -- ^ Validator
                   -> BS.ByteString -- ^ Redeemer
                   -> BS.ByteString -- ^ Data
                   -> Bool
validateByteString _ _ _ = True

validateResponse :: ToValidate -> (Status, BSL.ByteString)
validateResponse (ToValidate v r d) =
    if validateByteString (getByteString64 v) (getByteString64 r) (getByteString64 d)
        then (status200, trueJSON)
        else (status200, falseJSON)

-- typecheck, run/validate
app :: Application
app req respond = do
    bsReq <- lazyRequestBody req
    let decoded = decode bsReq
        validated = fmap validateResponse decoded
        -- TODO: handle json errors
        (stat, resp) = case validated of
            Just x  -> x
            Nothing -> (status400, falseJSON)
    respond $ responseLBS stat [] resp
