{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString.Lazy      as BSL
import           Network.HTTP.Types.Status
import           Network.Wai
import           Network.Wai.Handler.Warp

main :: IO ()
main = run 3000 app

trueJSON :: BSL.ByteString
trueJSON = "{\"isValid\":true}"

falseJSON :: BSL.ByteString
falseJSON = "{\"isValid\":false}"

-- typecheck, run/validate

app :: Application
app req respond =
    let bsReq = strictRequestBody
    in
    -- TODO: what to do when error is returned?
    respond $ responseLBS status200 [] trueJSON -- TODO: return actual answer we want instead of always saying it's valid
