{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Cardano.Wallet.ServerSpec
    ( tests
    ) where

import           Cardano.Wallet.Mock
import           Control.Monad                        (replicateM)
import qualified Data.ByteString                      as BS
import           Data.Word
import           Test.QuickCheck.Arbitrary            (Arbitrary, arbitrary)
import           Test.QuickCheck.Instances.ByteString
import           Test.Tasty
import           Test.Tasty.HUnit                     (assertEqual, testCase)
import           Test.Tasty.QuickCheck


tests :: TestTree
tests = testGroup "Cardano.Wallet.Mock" [testProperty "ByteString <-> Integer" byteStringIntegerIsomorphism]

byteStringIntegerIsomorphism :: Property
byteStringIntegerIsomorphism = property $ do
    forAll genBytes $ \bytes -> do
        let bs = BS.pack bytes
        integer2ByteString32 (byteString2Integer bs) === bs
  where
      genBytes :: Gen [Word8]
      genBytes = replicateM 32 arbitrary
