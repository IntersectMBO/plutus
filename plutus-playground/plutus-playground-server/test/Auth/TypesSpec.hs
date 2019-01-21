{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Auth.TypesSpec
  ( spec
  ) where

import           Data.Aeson                     (eitherDecode)
import qualified Data.ByteString.Lazy           as LBS
import           Paths_plutus_playground_server (getDataFileName)
import           Test.Hspec                     (Spec, describe, it, shouldBe)
import           Auth.Types                     (OAuthToken (OAuthToken), Token (Token), TokenProvider (Github),
                                                 oAuthTokenAccessToken, oAuthTokenScope, oAuthTokenTokenType)

spec :: Spec
spec = oAuthTokenJsonHandlingSpec

oAuthTokenJsonHandlingSpec :: Spec
oAuthTokenJsonHandlingSpec =
  describe "OAuthToken JSON handling" $
  it "should be able to parse a github response" $ do
    input1 <- LBS.readFile =<< getDataFileName "test/oAuthToken1.json"
    let decoded :: Either String (OAuthToken 'Github) = eitherDecode input1
    decoded `shouldBe`
      Right
        (OAuthToken
           { oAuthTokenAccessToken =
               Token "ee3d47a281b8540a2d970a4bf5eb93cdaeb0ed52"
           , oAuthTokenScope = "gist"
           , oAuthTokenTokenType = "bearer"
           })
