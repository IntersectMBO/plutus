{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module SchemaSpec
    ( spec
    ) where

import           Data.Functor.Foldable (Fix (Fix))
import           Data.Text             (Text)
import           GHC.Generics          (Generic)
import           Ledger.Ada            (lovelaceValueOf)
import           Playground.Types      (PayToWalletParams (PayToWalletParams), payTo, value)
import           Schema                (FormArgumentF (FormArrayF, FormBoolF, FormIntF, FormObjectF, FormStringF, FormValueF),
                                        FormSchema (FormSchemaArray, FormSchemaBool, FormSchemaInt, FormSchemaMaybe, FormSchemaObject, FormSchemaString, FormSchemaTuple),
                                        ToArgument, ToSchema, toArgument, toSchema)
import           Test.Hspec            (Spec, describe, it, shouldBe)
import           Wallet.Emulator.Types (Wallet (Wallet))

spec :: Spec
spec = do
    toSchemaTests
    toArgumentTests

toSchemaTests :: Spec
toSchemaTests =
    describe "toSchema" $
    describe "Encoding of various types" $ do
        it "Int" $ toSchema @Int `shouldBe` FormSchemaInt
        it "Integer" $ toSchema @Integer `shouldBe` FormSchemaInt
        it "String" $ toSchema @String `shouldBe` FormSchemaString
        it "Text" $ toSchema @Text `shouldBe` FormSchemaString
        it "[Int]" $ toSchema @[Int] `shouldBe` FormSchemaArray FormSchemaInt
        it "(Int, String)" $
            toSchema @(Int, String) `shouldBe`
            FormSchemaTuple FormSchemaInt FormSchemaString
        it "Maybe String" $
            toSchema @(Maybe String) `shouldBe` FormSchemaMaybe FormSchemaString
        it "User" $
            toSchema @User `shouldBe`
            FormSchemaObject
                [ ("userName", FormSchemaString)
                , ("userAge", FormSchemaInt)
                , ("userAlive", FormSchemaBool)
                ]

toArgumentTests :: Spec
toArgumentTests =
    describe "toArgument" $
    describe "Encoding of various types" $ do
        it "Bool" $ toArgument False `shouldBe` (Fix $ FormBoolF False)
        it "Int" $ toArgument (5 :: Int) `shouldBe` (Fix $ FormIntF $ Just 5)
        it "String" $
            toArgument ("Test" :: String) `shouldBe`
            (Fix $ FormStringF $ Just "Test")
        it "[String]" $
            toArgument ([1, 2, 3] :: [Int]) `shouldBe`
            Fix
                (FormArrayF
                     FormSchemaInt
                     [ Fix $ FormIntF $ Just 1
                     , Fix $ FormIntF $ Just 2
                     , Fix $ FormIntF $ Just 3
                     ])
        it "User" $
            toArgument
                User {userName = "Tester", userAge = 21, userAlive = True} `shouldBe`
            Fix
                (FormObjectF
                     [ ("userName", Fix (FormStringF $ Just "Tester"))
                     , ("userAge", Fix (FormIntF $ Just 21))
                     , ("userAlive", Fix (FormBoolF True))
                     ])
        it "PayToWalletParams" $ do
            let payTo = Wallet 1
                value = lovelaceValueOf 20
            toArgument PayToWalletParams {payTo, value} `shouldBe`
                Fix
                    (FormObjectF
                         [ ( "payTo"
                           , Fix (FormObjectF
                                      [("getWallet", Fix (FormIntF $ Just 1))]))
                         , ("value", Fix (FormValueF value))
                         ])

data User =
    User
        { userName  :: Text
        , userAge   :: Int
        , userAlive :: Bool
        }
    deriving (Show, Eq, Generic, ToSchema, ToArgument)
