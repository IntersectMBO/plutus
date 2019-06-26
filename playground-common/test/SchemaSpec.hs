{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module SchemaSpec where

import           Crypto.Hash  (Digest, SHA256)
import           Data.Proxy   (Proxy (Proxy))
import           Data.Text    (Text)
import           GHC.Generics (Generic)
import           Schema       (Constructor (Constructor, Record), ConstructorName (ConstructorName),
                               DataType (DataType), Reference (Reference), ToSchema, ToTypeName, toSchema)
import           Test.Hspec   (Spec, describe, hspec, it, shouldBe)

k :: IO ()
k = hspec spec

spec :: Spec
spec = toSchemaSpec

toSchemaSpec :: Spec
toSchemaSpec =
    describe "To schema" $ do
        it "Int" $ toSchema (Proxy :: Proxy Int) `shouldBe` DataType "Int" [] []
        it "Integer" $
            toSchema (Proxy :: Proxy Int) `shouldBe` DataType "Int" [] []
        it "String" $
            toSchema (Proxy :: Proxy String) `shouldBe` DataType "String" [] []
        it "Text" $
            toSchema (Proxy :: Proxy Text) `shouldBe` DataType "String" [] []
        it "Hash" $
            toSchema (Proxy @(Digest SHA256)) `shouldBe`
            DataType "Crypto.Hash.Digest" [] []
        it "Array Int" $
            toSchema (Proxy :: Proxy [Int]) `shouldBe`
            DataType "List" [] [Constructor "List" [Reference "Int"]]
        it "Maybe String" $
            toSchema (Proxy :: Proxy (Maybe String)) `shouldBe`
            DataType
                "GHC.Maybe.Maybe"
                []
                [ Constructor "Nothing" []
                , Constructor "Just" [Reference "String"]
                ]
        it "User" $
            toSchema (Proxy :: Proxy User) `shouldBe`
            DataType
                "SchemaSpec.User"
                []
                [ Record
                      (ConstructorName "User")
                      [ ("userName", Reference "String")
                      , ("userAge", Reference "Int")
                      , ("userAlive", Reference "Bool")
                      ]
                ]

data User =
    User
        { userName  :: Text
        , userAge   :: Int
        , userAlive :: Bool
        }
    deriving (Show, Eq, Generic, ToSchema, ToTypeName)
