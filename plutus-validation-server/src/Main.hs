{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Data.Aeson
import           Data.Aeson.Types
import qualified Data.ByteString             as BS
import qualified Data.ByteString.Base64.Type as BS64
import qualified Data.ByteString.Lazy        as BSL
import           Network.HTTP.Types.Status
import           Network.Wai
import           Network.Wai.Handler.Warp

main :: IO ()
main = run 3000 app

trueJSON :: BSL.ByteString
trueJSON = "{\"isValid\":true}"

validateByteString :: BS.ByteString -- ^ Validator
                   -> BS.ByteString -- ^ Redeemer
                   -> BS.ByteString -- ^ Data
                   -> Bool
validateByteString _ _ _ = True

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

-- typecheck, run/validate

app :: Application
app req respond =
    let bsReq = strictRequestBody req
    in
    -- TODO: what to do when error is returned?
    respond $ responseLBS status200 [] trueJSON -- TODO: return actual answer we want instead of always saying it's valid
