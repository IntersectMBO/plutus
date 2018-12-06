{-# LANGUAGE OverloadedStrings #-}

module Playground.APISpec
  ( spec
  ) where

import           Data.HashMap.Strict.InsOrd (fromList)
import           Data.Swagger               (ParamSchema (ParamSchema), Referenced (Inline), Schema (Schema),
                                             SwaggerType (SwaggerInteger, SwaggerObject, SwaggerString),
                                             _paramSchemaDefault, _paramSchemaEnum, _paramSchemaExclusiveMaximum,
                                             _paramSchemaExclusiveMinimum, _paramSchemaFormat, _paramSchemaItems,
                                             _paramSchemaMaxItems, _paramSchemaMaxLength, _paramSchemaMaximum,
                                             _paramSchemaMinItems, _paramSchemaMinLength, _paramSchemaMinimum,
                                             _paramSchemaMultipleOf, _paramSchemaPattern, _paramSchemaType,
                                             _paramSchemaUniqueItems, _schemaAdditionalProperties, _schemaAllOf,
                                             _schemaDescription, _schemaDiscriminator, _schemaExample,
                                             _schemaExternalDocs, _schemaMaxProperties, _schemaMinProperties,
                                             _schemaParamSchema, _schemaProperties, _schemaReadOnly, _schemaRequired,
                                             _schemaTitle, _schemaXml)
import           Data.Text                  ()
import           Playground.API             (CompilationError (CompilationError, RawError), SimpleArgumentSchema (SimpleIntArgument, SimpleObjectArgument, SimpleStringArgument),
                                             column, filename, parseErrorText, row, text, toSimpleArgumentSchema)
import           Test.Hspec                 (Spec, describe, it, shouldBe)

spec :: Spec
spec = do
  parseErrorTextSpec
  toSimpleArgumentSchemaSpec

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

toSimpleArgumentSchemaSpec :: Spec
toSimpleArgumentSchemaSpec =
  describe "toSimpleArgumentSchema" $ do
    it "should convert a simple integer argument" $
      toSimpleArgumentSchema integerSchema `shouldBe` SimpleIntArgument
    it "should convert a simple string argument" $
      toSimpleArgumentSchema stringSchema `shouldBe` SimpleStringArgument
    it "should convert an object argument" $
      toSimpleArgumentSchema objectSchema `shouldBe`
      SimpleObjectArgument
        [ ( "vestingTranche1"
          , SimpleObjectArgument
              [ ("vestingTrancheDate", SimpleIntArgument)
              , ("vestingTrancheAmount", SimpleIntArgument)
              ])
        , ( "vestingTranche2"
          , SimpleObjectArgument
              [ ("vestingTrancheDate", SimpleIntArgument)
              , ("vestingTrancheAmount", SimpleIntArgument)
              ])
        , ( "vestingOwner"
          , SimpleObjectArgument [("getPubKey", SimpleIntArgument)])
        ]

integerSchema :: Schema
integerSchema =
  Schema
    { _schemaTitle = Nothing
    , _schemaDescription = Nothing
    , _schemaRequired = []
    , _schemaAllOf = Nothing
    , _schemaProperties = fromList []
    , _schemaAdditionalProperties = Nothing
    , _schemaDiscriminator = Nothing
    , _schemaReadOnly = Nothing
    , _schemaXml = Nothing
    , _schemaExternalDocs = Nothing
    , _schemaExample = Nothing
    , _schemaMaxProperties = Nothing
    , _schemaMinProperties = Nothing
    , _schemaParamSchema =
        ParamSchema
          { _paramSchemaDefault = Nothing
          , _paramSchemaType = SwaggerInteger
          , _paramSchemaFormat = Nothing
          , _paramSchemaItems = Nothing
          , _paramSchemaMaximum = Just 9.223372036854775807e18
          , _paramSchemaExclusiveMaximum = Nothing
          , _paramSchemaMinimum = Just (-9.223372036854775808e18)
          , _paramSchemaExclusiveMinimum = Nothing
          , _paramSchemaMaxLength = Nothing
          , _paramSchemaMinLength = Nothing
          , _paramSchemaPattern = Nothing
          , _paramSchemaMaxItems = Nothing
          , _paramSchemaMinItems = Nothing
          , _paramSchemaUniqueItems = Nothing
          , _paramSchemaEnum = Nothing
          , _paramSchemaMultipleOf = Nothing
          }
    }

stringSchema :: Schema
stringSchema =
  Schema
    { _schemaTitle = Nothing
    , _schemaDescription = Nothing
    , _schemaRequired = []
    , _schemaAllOf = Nothing
    , _schemaProperties = fromList []
    , _schemaAdditionalProperties = Nothing
    , _schemaDiscriminator = Nothing
    , _schemaReadOnly = Nothing
    , _schemaXml = Nothing
    , _schemaExternalDocs = Nothing
    , _schemaExample = Nothing
    , _schemaMaxProperties = Nothing
    , _schemaMinProperties = Nothing
    , _schemaParamSchema =
        ParamSchema
          { _paramSchemaDefault = Nothing
          , _paramSchemaType = SwaggerString
          , _paramSchemaFormat = Nothing
          , _paramSchemaItems = Nothing
          , _paramSchemaMaximum = Nothing
          , _paramSchemaExclusiveMaximum = Nothing
          , _paramSchemaMinimum = Nothing
          , _paramSchemaExclusiveMinimum = Nothing
          , _paramSchemaMaxLength = Nothing
          , _paramSchemaMinLength = Nothing
          , _paramSchemaPattern = Nothing
          , _paramSchemaMaxItems = Nothing
          , _paramSchemaMinItems = Nothing
          , _paramSchemaUniqueItems = Nothing
          , _paramSchemaEnum = Nothing
          , _paramSchemaMultipleOf = Nothing
          }
    }

objectSchema :: Schema
objectSchema =
  Schema
    { _schemaTitle = Nothing
    , _schemaDescription = Nothing
    , _schemaRequired = ["vestingTranche1", "vestingTranche2", "vestingOwner"]
    , _schemaAllOf = Nothing
    , _schemaProperties =
        fromList
          [ ( "vestingTranche1"
            , Inline
                (Schema
                   { _schemaTitle = Nothing
                   , _schemaDescription = Nothing
                   , _schemaRequired =
                       ["vestingTrancheDate", "vestingTrancheAmount"]
                   , _schemaAllOf = Nothing
                   , _schemaProperties =
                       fromList
                         [ ( "vestingTrancheDate"
                           , Inline
                               (Schema
                                  { _schemaTitle = Nothing
                                  , _schemaDescription = Nothing
                                  , _schemaRequired = []
                                  , _schemaAllOf = Nothing
                                  , _schemaProperties = fromList []
                                  , _schemaAdditionalProperties = Nothing
                                  , _schemaDiscriminator = Nothing
                                  , _schemaReadOnly = Nothing
                                  , _schemaXml = Nothing
                                  , _schemaExternalDocs = Nothing
                                  , _schemaExample = Nothing
                                  , _schemaMaxProperties = Nothing
                                  , _schemaMinProperties = Nothing
                                  , _schemaParamSchema =
                                      ParamSchema
                                        { _paramSchemaDefault = Nothing
                                        , _paramSchemaType = SwaggerInteger
                                        , _paramSchemaFormat = Nothing
                                        , _paramSchemaItems = Nothing
                                        , _paramSchemaMaximum =
                                            Just 9.223372036854775807e18
                                        , _paramSchemaExclusiveMaximum = Nothing
                                        , _paramSchemaMinimum =
                                            Just (-9.223372036854775808e18)
                                        , _paramSchemaExclusiveMinimum = Nothing
                                        , _paramSchemaMaxLength = Nothing
                                        , _paramSchemaMinLength = Nothing
                                        , _paramSchemaPattern = Nothing
                                        , _paramSchemaMaxItems = Nothing
                                        , _paramSchemaMinItems = Nothing
                                        , _paramSchemaUniqueItems = Nothing
                                        , _paramSchemaEnum = Nothing
                                        , _paramSchemaMultipleOf = Nothing
                                        }
                                  }))
                         , ( "vestingTrancheAmount"
                           , Inline
                               (Schema
                                  { _schemaTitle = Nothing
                                  , _schemaDescription = Nothing
                                  , _schemaRequired = []
                                  , _schemaAllOf = Nothing
                                  , _schemaProperties = fromList []
                                  , _schemaAdditionalProperties = Nothing
                                  , _schemaDiscriminator = Nothing
                                  , _schemaReadOnly = Nothing
                                  , _schemaXml = Nothing
                                  , _schemaExternalDocs = Nothing
                                  , _schemaExample = Nothing
                                  , _schemaMaxProperties = Nothing
                                  , _schemaMinProperties = Nothing
                                  , _schemaParamSchema =
                                      ParamSchema
                                        { _paramSchemaDefault = Nothing
                                        , _paramSchemaType = SwaggerInteger
                                        , _paramSchemaFormat = Nothing
                                        , _paramSchemaItems = Nothing
                                        , _paramSchemaMaximum =
                                            Just 9.223372036854775807e18
                                        , _paramSchemaExclusiveMaximum = Nothing
                                        , _paramSchemaMinimum =
                                            Just (-9.223372036854775808e18)
                                        , _paramSchemaExclusiveMinimum = Nothing
                                        , _paramSchemaMaxLength = Nothing
                                        , _paramSchemaMinLength = Nothing
                                        , _paramSchemaPattern = Nothing
                                        , _paramSchemaMaxItems = Nothing
                                        , _paramSchemaMinItems = Nothing
                                        , _paramSchemaUniqueItems = Nothing
                                        , _paramSchemaEnum = Nothing
                                        , _paramSchemaMultipleOf = Nothing
                                        }
                                  }))
                         ]
                   , _schemaAdditionalProperties = Nothing
                   , _schemaDiscriminator = Nothing
                   , _schemaReadOnly = Nothing
                   , _schemaXml = Nothing
                   , _schemaExternalDocs = Nothing
                   , _schemaExample = Nothing
                   , _schemaMaxProperties = Nothing
                   , _schemaMinProperties = Nothing
                   , _schemaParamSchema =
                       ParamSchema
                         { _paramSchemaDefault = Nothing
                         , _paramSchemaType = SwaggerObject
                         , _paramSchemaFormat = Nothing
                         , _paramSchemaItems = Nothing
                         , _paramSchemaMaximum = Nothing
                         , _paramSchemaExclusiveMaximum = Nothing
                         , _paramSchemaMinimum = Nothing
                         , _paramSchemaExclusiveMinimum = Nothing
                         , _paramSchemaMaxLength = Nothing
                         , _paramSchemaMinLength = Nothing
                         , _paramSchemaPattern = Nothing
                         , _paramSchemaMaxItems = Nothing
                         , _paramSchemaMinItems = Nothing
                         , _paramSchemaUniqueItems = Nothing
                         , _paramSchemaEnum = Nothing
                         , _paramSchemaMultipleOf = Nothing
                         }
                   }))
          , ( "vestingTranche2"
            , Inline
                (Schema
                   { _schemaTitle = Nothing
                   , _schemaDescription = Nothing
                   , _schemaRequired =
                       ["vestingTrancheDate", "vestingTrancheAmount"]
                   , _schemaAllOf = Nothing
                   , _schemaProperties =
                       fromList
                         [ ( "vestingTrancheDate"
                           , Inline
                               (Schema
                                  { _schemaTitle = Nothing
                                  , _schemaDescription = Nothing
                                  , _schemaRequired = []
                                  , _schemaAllOf = Nothing
                                  , _schemaProperties = fromList []
                                  , _schemaAdditionalProperties = Nothing
                                  , _schemaDiscriminator = Nothing
                                  , _schemaReadOnly = Nothing
                                  , _schemaXml = Nothing
                                  , _schemaExternalDocs = Nothing
                                  , _schemaExample = Nothing
                                  , _schemaMaxProperties = Nothing
                                  , _schemaMinProperties = Nothing
                                  , _schemaParamSchema =
                                      ParamSchema
                                        { _paramSchemaDefault = Nothing
                                        , _paramSchemaType = SwaggerInteger
                                        , _paramSchemaFormat = Nothing
                                        , _paramSchemaItems = Nothing
                                        , _paramSchemaMaximum =
                                            Just 9.223372036854775807e18
                                        , _paramSchemaExclusiveMaximum = Nothing
                                        , _paramSchemaMinimum =
                                            Just (-9.223372036854775808e18)
                                        , _paramSchemaExclusiveMinimum = Nothing
                                        , _paramSchemaMaxLength = Nothing
                                        , _paramSchemaMinLength = Nothing
                                        , _paramSchemaPattern = Nothing
                                        , _paramSchemaMaxItems = Nothing
                                        , _paramSchemaMinItems = Nothing
                                        , _paramSchemaUniqueItems = Nothing
                                        , _paramSchemaEnum = Nothing
                                        , _paramSchemaMultipleOf = Nothing
                                        }
                                  }))
                         , ( "vestingTrancheAmount"
                           , Inline
                               (Schema
                                  { _schemaTitle = Nothing
                                  , _schemaDescription = Nothing
                                  , _schemaRequired = []
                                  , _schemaAllOf = Nothing
                                  , _schemaProperties = fromList []
                                  , _schemaAdditionalProperties = Nothing
                                  , _schemaDiscriminator = Nothing
                                  , _schemaReadOnly = Nothing
                                  , _schemaXml = Nothing
                                  , _schemaExternalDocs = Nothing
                                  , _schemaExample = Nothing
                                  , _schemaMaxProperties = Nothing
                                  , _schemaMinProperties = Nothing
                                  , _schemaParamSchema =
                                      ParamSchema
                                        { _paramSchemaDefault = Nothing
                                        , _paramSchemaType = SwaggerInteger
                                        , _paramSchemaFormat = Nothing
                                        , _paramSchemaItems = Nothing
                                        , _paramSchemaMaximum =
                                            Just 9.223372036854775807e18
                                        , _paramSchemaExclusiveMaximum = Nothing
                                        , _paramSchemaMinimum =
                                            Just (-9.223372036854775808e18)
                                        , _paramSchemaExclusiveMinimum = Nothing
                                        , _paramSchemaMaxLength = Nothing
                                        , _paramSchemaMinLength = Nothing
                                        , _paramSchemaPattern = Nothing
                                        , _paramSchemaMaxItems = Nothing
                                        , _paramSchemaMinItems = Nothing
                                        , _paramSchemaUniqueItems = Nothing
                                        , _paramSchemaEnum = Nothing
                                        , _paramSchemaMultipleOf = Nothing
                                        }
                                  }))
                         ]
                   , _schemaAdditionalProperties = Nothing
                   , _schemaDiscriminator = Nothing
                   , _schemaReadOnly = Nothing
                   , _schemaXml = Nothing
                   , _schemaExternalDocs = Nothing
                   , _schemaExample = Nothing
                   , _schemaMaxProperties = Nothing
                   , _schemaMinProperties = Nothing
                   , _schemaParamSchema =
                       ParamSchema
                         { _paramSchemaDefault = Nothing
                         , _paramSchemaType = SwaggerObject
                         , _paramSchemaFormat = Nothing
                         , _paramSchemaItems = Nothing
                         , _paramSchemaMaximum = Nothing
                         , _paramSchemaExclusiveMaximum = Nothing
                         , _paramSchemaMinimum = Nothing
                         , _paramSchemaExclusiveMinimum = Nothing
                         , _paramSchemaMaxLength = Nothing
                         , _paramSchemaMinLength = Nothing
                         , _paramSchemaPattern = Nothing
                         , _paramSchemaMaxItems = Nothing
                         , _paramSchemaMinItems = Nothing
                         , _paramSchemaUniqueItems = Nothing
                         , _paramSchemaEnum = Nothing
                         , _paramSchemaMultipleOf = Nothing
                         }
                   }))
          , ( "vestingOwner"
            , Inline
                (Schema
                   { _schemaTitle = Nothing
                   , _schemaDescription = Nothing
                   , _schemaRequired = ["getPubKey"]
                   , _schemaAllOf = Nothing
                   , _schemaProperties =
                       fromList
                         [ ( "getPubKey"
                           , Inline
                               (Schema
                                  { _schemaTitle = Nothing
                                  , _schemaDescription = Nothing
                                  , _schemaRequired = []
                                  , _schemaAllOf = Nothing
                                  , _schemaProperties = fromList []
                                  , _schemaAdditionalProperties = Nothing
                                  , _schemaDiscriminator = Nothing
                                  , _schemaReadOnly = Nothing
                                  , _schemaXml = Nothing
                                  , _schemaExternalDocs = Nothing
                                  , _schemaExample = Nothing
                                  , _schemaMaxProperties = Nothing
                                  , _schemaMinProperties = Nothing
                                  , _schemaParamSchema =
                                      ParamSchema
                                        { _paramSchemaDefault = Nothing
                                        , _paramSchemaType = SwaggerInteger
                                        , _paramSchemaFormat = Nothing
                                        , _paramSchemaItems = Nothing
                                        , _paramSchemaMaximum =
                                            Just 9.223372036854775807e18
                                        , _paramSchemaExclusiveMaximum = Nothing
                                        , _paramSchemaMinimum =
                                            Just (-9.223372036854775808e18)
                                        , _paramSchemaExclusiveMinimum = Nothing
                                        , _paramSchemaMaxLength = Nothing
                                        , _paramSchemaMinLength = Nothing
                                        , _paramSchemaPattern = Nothing
                                        , _paramSchemaMaxItems = Nothing
                                        , _paramSchemaMinItems = Nothing
                                        , _paramSchemaUniqueItems = Nothing
                                        , _paramSchemaEnum = Nothing
                                        , _paramSchemaMultipleOf = Nothing
                                        }
                                  }))
                         ]
                   , _schemaAdditionalProperties = Nothing
                   , _schemaDiscriminator = Nothing
                   , _schemaReadOnly = Nothing
                   , _schemaXml = Nothing
                   , _schemaExternalDocs = Nothing
                   , _schemaExample = Nothing
                   , _schemaMaxProperties = Nothing
                   , _schemaMinProperties = Nothing
                   , _schemaParamSchema =
                       ParamSchema
                         { _paramSchemaDefault = Nothing
                         , _paramSchemaType = SwaggerObject
                         , _paramSchemaFormat = Nothing
                         , _paramSchemaItems = Nothing
                         , _paramSchemaMaximum = Nothing
                         , _paramSchemaExclusiveMaximum = Nothing
                         , _paramSchemaMinimum = Nothing
                         , _paramSchemaExclusiveMinimum = Nothing
                         , _paramSchemaMaxLength = Nothing
                         , _paramSchemaMinLength = Nothing
                         , _paramSchemaPattern = Nothing
                         , _paramSchemaMaxItems = Nothing
                         , _paramSchemaMinItems = Nothing
                         , _paramSchemaUniqueItems = Nothing
                         , _paramSchemaEnum = Nothing
                         , _paramSchemaMultipleOf = Nothing
                         }
                   }))
          ]
    , _schemaAdditionalProperties = Nothing
    , _schemaDiscriminator = Nothing
    , _schemaReadOnly = Nothing
    , _schemaXml = Nothing
    , _schemaExternalDocs = Nothing
    , _schemaExample = Nothing
    , _schemaMaxProperties = Nothing
    , _schemaMinProperties = Nothing
    , _schemaParamSchema =
        ParamSchema
          { _paramSchemaDefault = Nothing
          , _paramSchemaType = SwaggerObject
          , _paramSchemaFormat = Nothing
          , _paramSchemaItems = Nothing
          , _paramSchemaMaximum = Nothing
          , _paramSchemaExclusiveMaximum = Nothing
          , _paramSchemaMinimum = Nothing
          , _paramSchemaExclusiveMinimum = Nothing
          , _paramSchemaMaxLength = Nothing
          , _paramSchemaMinLength = Nothing
          , _paramSchemaPattern = Nothing
          , _paramSchemaMaxItems = Nothing
          , _paramSchemaMinItems = Nothing
          , _paramSchemaUniqueItems = Nothing
          , _paramSchemaEnum = Nothing
          , _paramSchemaMultipleOf = Nothing
          }
    }
