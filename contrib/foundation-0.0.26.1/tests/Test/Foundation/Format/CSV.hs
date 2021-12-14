{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Foundation.Format.CSV
    ( testFormatCSV
    ) where

import Foundation
import Foundation.Format.CSV
import Foundation.Check
import Foundation.String.Builder (toString)
import Foundation.Parser (parseOnly)

import Data.Typeable

testFormatCSV :: Test
testFormatCSV = Group "CSV"
    [ Group "field unit tests" $ testFieldEncoding <$> fieldUnitTests
    , Group "row unit tests" $ testRowEncoding <$> rowUnitTests
    , Group "row unit tests" $ testRowDecoding <$> rowUnitTests
    , Group "record . toRow == id"
        [ pTest (Proxy @(Bool, Bool))
        , pTest (Proxy @(Int8, Word32, Natural))
        , pTest (Proxy @(Int, String, Word256, Word128))
        , pTest (Proxy @(Word8, String, Bool, Int64, String))
        ]
    ]

  where
    pTest :: (Arbitrary a, Record a, Typeable a, Show a, Eq a) => Proxy a -> Test
    pTest p = Property (show $ typeRep p) (go p)
      where
        go :: (Arbitrary a, Record a, Typeable a, Show a, Eq a) => Proxy a -> a -> PropertyCheck
        go _ t =
          let row = (toRow t)
              str = toString $ rowStringBuilder row
           in case parseOnly record_ str of
               Left err -> propertyFail $ show err
               Right v -> t === v
    testFieldEncoding (f,r) = Property (show f) $
      let str = toString (fieldStringBuilder f)
       in r === str
    testRowDecoding (r, row,result) = Property (show r) $
        case parseOnly record result of
            Left err -> propertyFail (show err)
            Right v  -> row === v
    testRowEncoding (row, _,result) = Property (show row) $
      let str = toString (rowStringBuilder row)
       in result === str

fieldUnitTests :: [(Field, String)]
fieldUnitTests =
    [ (FieldInteger 42, "42")
    , (FieldDouble  1, "1.0")
    , (FieldDouble  0.000001, "1.0e-6")
    , (FieldString  "String" NoEscape, "String")
    , (string "String", "String")
    , (string "with comma,string", "\"with comma,string\"")
    , (FieldString  "multiline\nstring" Escape, "\"multiline\nstring\"")
    , (FieldString  "piece of 12\" by 23\""  DoubleEscape, "\"piece of 12\"\" by 23\"\"\"")
    , (string "supported sizes are: 12\", 13\" and 14\"", "\"supported sizes are: 12\"\", 13\"\" and 14\"\"\"")
    ]

rowUnitTests :: [(Row, Row, String)]
rowUnitTests =
    [ ( fromList [toField (42 :: Int), toField ("some string" :: String)]
      , fromList [toField ("42" :: String), toField ("some string" :: String)]
      , "42,some string"
      )
    , ( toRow (42 :: Int, "some string" :: String)
      , toRow ("42" :: String, "some string" :: String)
      , "42,some string"
      )
    , ( toRow ( 42 :: Int
              , "some string" :: String
              , "supported sizes are: 12\", 13\" and 14\"" :: String
              )
      , toRow ( "42" :: String
              , "some string" :: String
              , "supported sizes are: 12\", 13\" and 14\"" :: String
              )
      , "42,some string,\"supported sizes are: 12\"\", 13\"\" and 14\"\"\""
      )
    , ( toRow ( 42 :: Int
              , "some string" :: String
              , "supported sizes are: 12\", 13\" and 14\"" :: String
              , Just 0.000001 :: Maybe Double
              )
      , toRow ( "42" :: String
              , "some string" :: String
              , "supported sizes are: 12\", 13\" and 14\"" :: String
              , Just "1.0e-6" :: Maybe String
              )
      , "42,some string,\"supported sizes are: 12\"\", 13\"\" and 14\"\"\",1.0e-6"
      )
    , ( toRow ( 42 :: Int
              , "some string" :: String
              , "supported sizes are: 12\", 13\" and 14\"" :: String
              , Just 0.000001 :: Maybe Double
              , Nothing       :: Maybe Char
              )
      , toRow ( "42" :: String
              , "some string" :: String
              , "supported sizes are: 12\", 13\" and 14\"" :: String
              , Just "1.0e-6"      :: Maybe String
              , Nothing       :: Maybe String
              )
      , "42,some string,\"supported sizes are: 12\"\", 13\"\" and 14\"\"\",1.0e-6,"
      )
    , ( toRow ( 42 :: Int
              , "some string" :: String
              , "supported sizes are: 12\", 13\" and 14\"" :: String
              , Just 0.000001 :: Maybe Double
              , Nothing       :: Maybe Char
              , "with £ € ¥" :: String
              )
      , toRow ( "42" :: String
              , "some string" :: String
              , "supported sizes are: 12\", 13\" and 14\"" :: String
              , Just "1.0e-6"      :: Maybe String
              , Nothing       :: Maybe String
              , "with £ € ¥" :: String
              )
      , "42,some string,\"supported sizes are: 12\"\", 13\"\" and 14\"\"\",1.0e-6,,with £ € ¥"
      )
    ]
