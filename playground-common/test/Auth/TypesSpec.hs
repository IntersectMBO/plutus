{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Auth.TypesSpec
    ( tests
    ) where

import           Auth.Types              (OAuthToken (OAuthToken), Token (Token), TokenProvider (Github),
                                          oAuthTokenAccessToken, oAuthTokenScope, oAuthTokenTokenType)
import           Data.Aeson              (eitherDecode)
import qualified Data.ByteString.Lazy    as LBS
import           Paths_playground_common (getDataFileName)
import           Test.Tasty              (TestTree, testGroup)
import           Test.Tasty.HUnit        (assertEqual, testCase)

tests :: TestTree
tests = testGroup "Auth.TypesSpec" [oAuthTokenJsonHandlingSpec]

oAuthTokenJsonHandlingSpec :: TestTree
oAuthTokenJsonHandlingSpec =
    testGroup
        "OAuthToken JSON handling"
        [ testCase "should be able to parse a github response" $ do
              input1 <- LBS.readFile =<< getDataFileName "test/oAuthToken1.json"
              let decoded :: Either String (OAuthToken 'Github) =
                      eitherDecode input1
              assertEqual
                  "AuthToken response."
                  decoded
                  (Right
                       (OAuthToken
                            { oAuthTokenAccessToken =
                                  Token
                                      "ee3d47a281b8540a2d970a4bf5eb93cdaeb0ed52"
                            , oAuthTokenScope = "gist"
                            , oAuthTokenTokenType = "bearer"
                            }))
        ]
