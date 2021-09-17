{-# OPTIONS_GHC -Wno-deprecations #-}
module Spec.Secrets (tests) where

import qualified Data.Aeson              as Aeson
import           Data.Maybe
import           Plutus.Contract.Secrets
import           Test.Tasty
import qualified Test.Tasty.QuickCheck   as QC

tests :: TestTree
tests = testGroup "secrets"
  [ QC.testProperty "isJust (decode (encode x))"
      $ \x -> isJust (Aeson.decode (Aeson.encode (secretArg (x :: Integer))) :: Maybe (SecretArgument Integer))
  , QC.testProperty "decode . encode = Just . mkSecret"
      $ \x -> (unsafe_escape_secret . extractSecret . fromJust . Aeson.decode . Aeson.encode . secretArg $ (x :: Integer)) == x
  , QC.testProperty "decode (encode x) is a secret"
      $ \x -> show ((fromJust . Aeson.decode . Aeson.encode . secretArg) (x :: Integer) :: SecretArgument Integer) == "EndpointSide *****"
  ]
