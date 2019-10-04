{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module SchemaSpec
    ( tests
    ) where

import           Data.Text        (Text)
import           GHC.Generics     (Generic)
import           Schema           (FormSchema (FormSchemaArray, FormSchemaBool, FormSchemaInt, FormSchemaMaybe, FormSchemaObject, FormSchemaString, FormSchemaTuple),
                                   ToSchema (toSchema))
import           Test.Tasty       (TestTree, testGroup)
import           Test.Tasty.HUnit (assertEqual, testCase)

tests :: TestTree
tests = testGroup "Schema" [toSchemaTests]

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
        ]

data User =
    User
        { userName  :: Text
        , userAge   :: Int
        , userAlive :: Bool
        }
    deriving (Show, Eq, Generic, ToSchema)
