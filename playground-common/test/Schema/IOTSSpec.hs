{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Schema.IOTSSpec where

import           Data.Algorithm.Diff          (Diff, getGroupedDiff)
import           Data.Algorithm.DiffOutput    (ppDiff)
import           Data.Function                (on)
import           Data.Map                     (Map)
import           Data.Proxy                   (Proxy (Proxy))
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import qualified Data.Text.IO                 as Text
import           GHC.Generics                 (Generic)
import           Paths_playground_common      (getDataFileName)
import           Schema                       (DataType, ToSchema, toSchema)
import           Schema.IOTS                  (export)
import           Test.Hspec                   (Spec, describe, it)
import           Test.HUnit                   (Assertion, assertBool, assertFailure)
import           Text.PrettyPrint.Leijen.Text (displayTStrict, renderPretty)

spec :: Spec
spec = toIOTSSpec

toIOTSSpec :: Spec
toIOTSSpec =
    describe "Export to IOTS format" $ do
        it "Should export a sample user" $
            exportsAs [toSchema (Proxy @User)] "test/Schema/IOTS/user.ts"
        it "Should export a single, fieldless constructor" $
            exportsAs
                [toSchema (Proxy @SingleFieldless)]
                "test/Schema/IOTS/singleFieldless.ts"
        it "Should export a simple sum type" $
            exportsAs
                [toSchema (Proxy @SimpleSum)]
                "test/Schema/IOTS/simpleSum.ts"
        it "Should export a more interesting sum type" $
            exportsAs
                [toSchema (Proxy @(Response String))]
                "test/Schema/IOTS/response.ts"
        it "Should export a complex type" $
            exportsAs
                [ toSchema (Proxy @Slot)
                , toSchema (Proxy @CurrencySymbol)
                , toSchema (Proxy @TokenName)
                , toSchema (Proxy @Value)
                , toSchema (Proxy @(Interval Slot))
                , toSchema (Proxy @VestingTranche)
                ]
                "test/Schema/IOTS/vestingTranche.ts"

exportsAs :: [DataType] -> FilePath -> IO ()
exportsAs exportables filename = do
    file <- Text.readFile =<< getDataFileName filename
    let exported = displayTStrict . renderPretty 0.8 200 <$> export exportables
    exported `shouldBePrettyDiff` file
  where
    shouldBePrettyDiff :: Either Text Text -> Text -> Assertion
    shouldBePrettyDiff (Left err) _ =
        assertFailure (formatError (Text.unpack err))
    shouldBePrettyDiff (Right a) b =
        assertBool
            (formatError (ppDiff (diffLines a b)))
            (Text.stripEnd a == Text.stripEnd b)

    diffLines :: Text -> Text -> [Diff [String]]
    diffLines = getGroupedDiff `on` lines . Text.unpack
    formatError err = unlines [filename, "Export failed with:", err]

data User =
    User
        { userId :: Int
        , name   :: String
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToSchema)

data VestingTranche =
    VestingTranche
        { vestingTrancheDate   :: Slot
        , vestingTrancheAmount :: Value
        , validity             :: Interval Slot
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToSchema)

newtype Slot =
    Slot
        { getSlot :: Integer
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

data Interval a =
    Interval
        { ivFrom :: Maybe a
        , ivTo   :: Maybe a
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

newtype CurrencySymbol =
    CurrencySymbol
        { unCurrencySymbol :: Text
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

newtype TokenName =
    TokenName
        { unTokenName :: Text
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

newtype Value =
    Value
        { getValue :: Map CurrencySymbol (Map TokenName Integer)
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

data SingleFieldless =
    VeryDull
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

data SimpleSum
    = This
    | That
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

data Response a
    = UnknownError Int Text
    | StatusError
          { code    :: Int
          , message :: Text
          , metrics :: Map String Int
          }
    | Response a
    | EmptyResponse
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)
