{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Schema.IOTSSpec where

import           Data.Algorithm.Diff       (Diff, getGroupedDiff)
import           Data.Algorithm.DiffOutput (ppDiff)
import           Data.Function             (on)
import           Data.Map                  (Map)
import           Data.Proxy                (Proxy (Proxy))
import           Data.Text                 (Text)
import qualified Data.Text                 as Text
import qualified Data.Text.IO              as Text
import           GHC.Generics              (Generic, Generic1)
import           Paths_playground_common   (getDataFileName)
import           Schema.IOTS               (HasReps, MyTypeable)
import qualified Schema.IOTS               as IOTS
import           Test.Hspec                (Spec, describe, it)
import           Test.HUnit                (Assertion, assertBool)

spec :: Spec
spec = toIOTSSpec

toIOTSSpec :: Spec
toIOTSSpec =
    describe "Export to IOTS format" $ do
        it "Should export a single, fieldless constructor" $
            exportsAs
                (Proxy @SingleFieldless)
                "test/Schema/IOTS/singleFieldless.ts"
        it "Should export a simple sum type" $
            exportsAs (Proxy @SimpleSum) "test/Schema/IOTS/simpleSum.ts"
        it "Should export a sample user" $
            exportsAs (Proxy @User) "test/Schema/IOTS/user.ts"
        it "Should export a more interesting sum type" $
            exportsAs (Proxy @(Response String)) "test/Schema/IOTS/response.ts"
        it "Should export a function with tuples." $ do
            let someFunction :: (CurrencySymbol, TokenName) -> String
                someFunction _ = "Anything."
            exportsAs someFunction "test/Schema/IOTS/functionTuple.ts"
        it "Should export a function with maybes." $ do
            let someFunction :: Maybe Slot -> String
                someFunction _ = "Anything."
            exportsAs someFunction "test/Schema/IOTS/functionMaybe.ts"
        it "Should export a function with lists." $ do
            let someFunction :: [User] -> String
                someFunction _ = "Anything."
            exportsAs someFunction "test/Schema/IOTS/functionList.ts"
        it "Should export a complex type" $ do
            let someFunction ::
                       (CurrencySymbol, TokenName)
                    -> Maybe Value
                    -> Interval Slot
                    -> [VestingTranche]
                    -> String
                someFunction _ _ _ _ = "Anything."
            exportsAs someFunction "test/Schema/IOTS/vestingTranche.ts"

exportsAs :: (MyTypeable a) => a -> FilePath -> IO ()
exportsAs exportable filename = do
    file <- Text.readFile =<< getDataFileName filename
    let exported = IOTS.render $ IOTS.export exportable
    exported `shouldBePrettyDiff` file
  where
    shouldBePrettyDiff :: Text -> Text -> Assertion
    shouldBePrettyDiff a b =
        assertBool
            (formatError (ppDiff (diffLines a b)))
            (Text.stripEnd a == Text.stripEnd b)
    diffLines :: Text -> Text -> [Diff [String]]
    diffLines = getGroupedDiff `on` lines . Text.unpack
    formatError err = unlines [filename, "Export failed with:", err]

data SingleFieldless =
    VeryDull
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (HasReps)

data SimpleSum
    = This
    | That
    | TheOther
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (HasReps)

data User =
    User
        { userId   :: Int
        , name     :: String
        , children :: [User]
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (HasReps)

data Response a
    = UnknownError Int Text
    | StatusError
          { code    :: Int
          , message :: Text
          , headers :: Map String Int
          }
    | EmptyResponse
    | Response a
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (HasReps)

newtype Slot =
    Slot
        { getSlot :: Integer
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (HasReps)

newtype CurrencySymbol =
    CurrencySymbol
        { unCurrencySymbol :: Text
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (HasReps)

newtype TokenName =
    TokenName
        { unTokenName :: Text
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (HasReps)

newtype AssocMap k v =
    AssocMap
        { unMap :: [(k, v)]
        }
    deriving (Show, Eq, Ord, Generic, Generic1)
    deriving anyclass (HasReps)

newtype Value =
    Value
        { getValue :: AssocMap CurrencySymbol (AssocMap TokenName Integer)
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (HasReps)

data Interval a =
    Interval
        { ivFrom :: Maybe a
        , ivTo   :: Maybe a
        }
    deriving (Show, Eq, Ord, Generic, Generic1)
    deriving anyclass (HasReps)

data VestingTranche =
    VestingTranche
        { vestingTrancheDate   :: Slot
        , vestingTrancheAmount :: Value
        , validity             :: Interval Slot
        }
    deriving (Show, Eq, Generic)
    deriving anyclass (HasReps)
