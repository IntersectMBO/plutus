{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module SchemaSpec where

import           Data.Text    (Text)
import           GHC.Generics (Generic)
import           Schema       (Constructor (Constructor, Record), ConstructorName (ConstructorName),
                               DataType (DataType), ToSchema, TypeSignature (TypeSignature), argumentSignatures,
                               constructorName, moduleName, toSchema, toTypeSignature)
import           Test.Hspec   (Spec, describe, it, shouldBe)

spec :: Spec
spec = toSchemaSpec

toSchemaSpec :: Spec
toSchemaSpec =
    describe "toSchema" $ do
        it "Int" $ toSchema @Int `shouldBe` intType
        it "Integer" $ toSchema @Integer `shouldBe` integerType
        it "String" $ toSchema @String `shouldBe` stringType
        it "Text" $
            toSchema @Text `shouldBe`
            DataType
                (TypeSignature
                     { moduleName = "Data.Text.Internal"
                     , constructorName = "Text"
                     , argumentSignatures = []
                     })
                []
        it "[Int]" $
            toSchema @[Int] `shouldBe`
            DataType
                (TypeSignature
                     { moduleName = "GHC.Types"
                     , constructorName = "[]"
                     , argumentSignatures = [toTypeSignature intType]
                     })
                []
        it "(Int, String)" $
            toSchema @(Int, String) `shouldBe`
            DataType
                (TypeSignature
                     { moduleName = "GHC.Tuple"
                     , constructorName = "(,)"
                     , argumentSignatures =
                           toTypeSignature <$> [intType, stringType]
                     })
                [Constructor (ConstructorName "Tuple") [intType, stringType]]
        it "Maybe String" $
            toSchema @(Maybe String) `shouldBe`
            DataType
                (TypeSignature
                     { moduleName = "GHC.Maybe"
                     , constructorName = "Maybe"
                     , argumentSignatures = [toTypeSignature stringType]
                     })
                [ Constructor (ConstructorName "Nothing") []
                , Constructor (ConstructorName "Just") [stringType]
                ]
        it "User" $
            toSchema @User `shouldBe`
            DataType
                (TypeSignature
                     { moduleName = "SchemaSpec"
                     , constructorName = "User"
                     , argumentSignatures = []
                     })
                [ Record
                      (ConstructorName "User")
                      [ ("userName", textType)
                      , ("userAge", intType)
                      , ("userAlive", boolType)
                      ]
                ]

data User =
    User
        { userName  :: Text
        , userAge   :: Int
        , userAlive :: Bool
        }
    deriving (Show, Eq, Generic, ToSchema)

intType :: DataType
intType =
    DataType
        (TypeSignature
             { moduleName = "GHC.Types"
             , constructorName = "Int"
             , argumentSignatures = []
             })
        []

integerType :: DataType
integerType =
    DataType
        (TypeSignature
             { moduleName = "GHC.Integer.Type"
             , constructorName = "Integer"
             , argumentSignatures = []
             })
        []

stringType :: DataType
stringType =
    DataType
        (TypeSignature
             { moduleName = "GHC.Types"
             , constructorName = "String"
             , argumentSignatures = []
             })
        []

textType :: DataType
textType =
    DataType
        (TypeSignature
             { moduleName = "Data.Text.Internal"
             , constructorName = "Text"
             , argumentSignatures = []
             })
        []

boolType :: DataType
boolType =
    DataType
        (TypeSignature
             { moduleName = "GHC.Types"
             , constructorName = "Bool"
             , argumentSignatures = []
             })
        []
