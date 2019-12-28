{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module SchemaSpec
    ( tests
    ) where

import           Data.Functor.Foldable (Fix (Fix))
import           Data.Text             (Text)
import           GHC.Generics          (Generic)
import           Ledger.Ada            (lovelaceValueOf)
import           Ledger.Value          (Value)
import           Playground.Types      (PayToWalletParams (PayToWalletParams), payTo, value)
import           Schema                (FormArgument, FormArgumentF (FormArrayF, FormBoolF, FormIntF, FormObjectF, FormRadioF, FormStringF, FormValueF),
                                        FormSchema (FormSchemaArray, FormSchemaBool, FormSchemaInt, FormSchemaMaybe, FormSchemaObject, FormSchemaRadio, FormSchemaString, FormSchemaTuple),
                                        ToArgument, ToSchema, toArgument, toSchema)
import           Test.Tasty            (TestTree, testGroup)
import           Test.Tasty.HUnit      (assertEqual, testCase)
import           Wallet.Emulator.Types (Wallet (Wallet))

tests :: TestTree
tests = testGroup "Schema" [toSchemaTests, toArgumentTests]

toSchemaTests :: TestTree
toSchemaTests =
    testGroup
        "toSchema"
        [ testCase "Encoding of various types" $ do
              assertEqual "Int" (toSchema @Int) FormSchemaInt
              assertEqual "Integer" (toSchema @Integer) FormSchemaInt
              assertEqual "String" (toSchema @String) FormSchemaString
              assertEqual "Text" (toSchema @Text) FormSchemaString
              assertEqual
                  "[Int]"
                  (toSchema @[Int])
                  (FormSchemaArray FormSchemaInt)
              assertEqual
                  "(Int, String)"
                  (toSchema @(Int, String))
                  (FormSchemaTuple FormSchemaInt FormSchemaString)
              assertEqual
                  "Maybe String"
                  (toSchema @(Maybe String))
                  (FormSchemaMaybe FormSchemaString)
              assertEqual
                  "User"
                  (toSchema @User)
                  (FormSchemaObject
                       [ ("userName", FormSchemaString)
                       , ("userAge", FormSchemaInt)
                       , ("userAlive", FormSchemaBool)
                       ])
              assertEqual
                  "Size"
                  (toSchema @Size)
                  (FormSchemaRadio ["Small", "Medium", "Large"])
        ]

toArgumentTests :: TestTree
toArgumentTests =
    testGroup
        "toArgument"
        [ testCase "Encoding of various types" $ do
              assertEqual "Bool" (toArgument False) (formBoolF False)
              assertEqual "Int" (toArgument (5 :: Int)) (formIntF 5)
              assertEqual
                  "String"
                  (toArgument ("Test" :: String))
                  (formStringF "Test")
              assertEqual
                  "[String]"
                  (toArgument ([1, 2, 3] :: [Int]))
                  (formArrayF FormSchemaInt (formIntF <$> [1, 2, 3]))
              assertEqual
                  "User"
                  (toArgument
                       User
                           {userName = "Tester", userAge = 21, userAlive = True})
                  (formObjectF
                       [ ("userName", formStringF "Tester")
                       , ("userAge", formIntF 21)
                       , ("userAlive", formBoolF True)
                       ])
              assertEqual
                  "Size"
                  (toArgument Medium)
                  (formRadioF ["Small", "Medium", "Large"] (Just "Medium"))
              let payTo = Wallet 1
                  value = lovelaceValueOf 20
              assertEqual
                  "PayToWalletParams"
                  (toArgument PayToWalletParams {payTo, value})
                  (formObjectF
                       [ ("payTo", formObjectF [("getWallet", formIntF 1)])
                       , ("value", formValueF value)
                       ])
        ]

data User =
    User
        { userName  :: Text
        , userAge   :: Int
        , userAlive :: Bool
        }
    deriving (Show, Eq, Generic, ToSchema, ToArgument)

data Size
    = Small
    | Medium
    | Large
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

formRadioF :: [String] -> Maybe String -> FormArgument
formRadioF options selection = Fix $ FormRadioF options selection

formObjectF :: [(String, FormArgument)] -> FormArgument
formObjectF = Fix . FormObjectF

formArrayF :: FormSchema -> [FormArgument] -> FormArgument
formArrayF t = Fix . FormArrayF t
