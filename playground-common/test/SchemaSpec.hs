{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module SchemaSpec where

import           Data.Text    (Text)
import           GHC.Generics (Generic)
import           Schema       (FormSchema (FormSchemaArray, FormSchemaBool, FormSchemaInt, FormSchemaMaybe, FormSchemaObject, FormSchemaString, FormSchemaTuple),
                               ToSchema (toSchema))
import           Test.Hspec   (Spec, describe, it, shouldBe)

spec :: Spec
spec = toSchemaSpec

toSchemaSpec :: Spec
toSchemaSpec =
    describe "toSchema" $ do
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

data User =
    User
        { userName  :: Text
        , userAge   :: Int
        , userAlive :: Bool
        }
    deriving (Show, Eq, Generic, ToSchema)
