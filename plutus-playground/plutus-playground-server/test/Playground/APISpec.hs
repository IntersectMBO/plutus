{-# LANGUAGE OverloadedStrings #-}

module Playground.APISpec
  ( spec
  ) where

import           Control.Exception (evaluate)
import           Data.Text         ()
import           Playground.API    (CompilationError (CompilationError, RawError), column, filename, parseErrorText,
                                    row, text)
import           Test.Hspec        (Spec, describe, it, shouldBe)

spec :: Spec
spec = parseErrorTextSpec

parseErrorTextSpec :: Spec
parseErrorTextSpec =
  describe "parseErrorText" $ do
    it "shouldn't be able to parse an empty string." $
      parseErrorText "" `shouldBe` RawError ""
    it "should handle a basic error" $
      parseErrorText
        "Contract4205-5.hs:13:6: error: parse error on input \8216..\8217" `shouldBe`
      (CompilationError
         { filename = "Contract4205-5.hs"
         , row = 13
         , column = 6
         , text = [" error: parse error on input \8216..\8217"]
         })
    it "should handle multiline errors" $
      parseErrorText
        "Main70317-3.hs:76:14: error:\n    \8226 Could not deduce (MonadError WalletAPIError m0)\n      from the context: (MonadError WalletAPIError m, WalletAPI m)\n        bound by the type signature for:\n                   vestFunds :: forall (m :: * -> *).\n                                (MonadError WalletAPIError m, WalletAPI m) =>\n                                Vesting -> Value -> IO ()\n        at Main70317-3.hs:(76,14)-(81,12)\n      The type variable \8216m0\8217 is ambiguous\n    \8226 In the ambiguity check for \8216vestFunds\8217\n      To defer the ambiguity check to use sites, enable AllowAmbiguousTypes\n      In the type signature:\n        vestFunds :: (MonadError WalletAPIError m, WalletAPI m) =>\n                     Vesting -> Value -> IO ()" `shouldBe`
      (CompilationError
         { filename = "Main70317-3.hs"
         , row = 76
         , column = 14
         , text =
             [ " error:"
             , "    \8226 Could not deduce (MonadError WalletAPIError m0)"
             , "      from the context: (MonadError WalletAPIError m, WalletAPI m)"
             , "        bound by the type signature for:"
             , "                   vestFunds :: forall (m :: * -> *)."
             , "                                (MonadError WalletAPIError m, WalletAPI m) =>"
             , "                                Vesting -> Value -> IO ()"
             , "        at Main70317-3.hs:(76,14)-(81,12)"
             , "      The type variable \8216m0\8217 is ambiguous"
             , "    \8226 In the ambiguity check for \8216vestFunds\8217"
             , "      To defer the ambiguity check to use sites, enable AllowAmbiguousTypes"
             , "      In the type signature:"
             , "        vestFunds :: (MonadError WalletAPIError m, WalletAPI m) =>"
             , "                     Vesting -> Value -> IO ()"
             ]
         })
