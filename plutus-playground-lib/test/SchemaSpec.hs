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
import           Ledger.Value          (Value)
import           Playground.Types      (PayToWalletParams (PayToWalletParams), payTo, value)
import           Schema                (FormArgument, FormArgumentF (FormArrayF, FormBoolF, FormIntF, FormObjectF, FormStringF, FormValueF),
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
        it "Bool" $ toArgument False `shouldBe` formBoolF False
        it "Int" $ toArgument (5 :: Int) `shouldBe` formIntF 5
        it "String" $
            toArgument ("Test" :: String) `shouldBe` formStringF "Test"
        it "[String]" $
            toArgument ([1, 2, 3] :: [Int]) `shouldBe`
            formArrayF FormSchemaInt (formIntF <$> [1, 2, 3])
        it "User" $
            toArgument
                User {userName = "Tester", userAge = 21, userAlive = True} `shouldBe`
            formObjectF
                [ ("userName", formStringF "Tester")
                , ("userAge", formIntF 21)
                , ("userAlive", formBoolF True)
                ]
        it "PayToWalletParams" $ do
            let payTo = Wallet 1
                value = lovelaceValueOf 20
            toArgument PayToWalletParams {payTo, value} `shouldBe`
                formObjectF
                    [ ("payTo", formObjectF [("getWallet", formIntF 1)])
                    , ("value", formValueF value)
                    ]

data User =
    User
        { userName  :: Text
        , userAge   :: Int
        , userAlive :: Bool
        }
    deriving (Show, Eq, Generic, ToSchema, ToArgument)

------------------------------------------------------------
-- A few helper constructors.
------------------------------------------------------------
formIntF :: Int -> FormArgument
formIntF = Fix . FormIntF . Just

formBoolF :: Bool -> FormArgument
formBoolF = Fix . FormBoolF

formStringF :: String -> FormArgument
formStringF = Fix . FormStringF . Just

formValueF :: Value -> FormArgument
formValueF = Fix . FormValueF

formObjectF :: [(String, FormArgument)] -> FormArgument
formObjectF = Fix . FormObjectF

formArrayF :: FormSchema -> [FormArgument] -> FormArgument
formArrayF t = Fix . FormArrayF t
