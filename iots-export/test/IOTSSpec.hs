{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE TypeApplications #-}

module IOTSSpec where

import           Data.Algorithm.Diff       (Diff, getGroupedDiff)
import           Data.Algorithm.DiffOutput (ppDiff)
import           Data.Function             (on)
import           Data.Map                  (Map)
import           Data.Proxy                (Proxy (Proxy))
import           Data.Text                 (Text)
import qualified Data.Text                 as Text
import qualified Data.Text.IO              as Text
import           GHC.Generics              (Generic)
import           IOTS                      (HList (HCons, HNil), IotsExportable, IotsType, Tagged (Tagged), export)
import           Paths_iots_export         (getDataFileName)
import           Test.Hspec                (Spec, describe, it)
import           Test.HUnit                (Assertion, assertBool)

spec :: Spec
spec = toIOTSSpec

toIOTSSpec :: Spec
toIOTSSpec =
  describe "Export to IOTS format" $ do
    it "Should export a single, fieldless constructor" $
      exportsAs (Proxy @SingleFieldless) "test/IOTS/singleFieldless.ts"
    it "Should export a simple sum type" $
      exportsAs (Proxy @SimpleSum) "test/IOTS/simpleSum.ts"
    it "Should export a sample user" $
      exportsAs (Proxy @User) "test/IOTS/user.ts"
    it "Should export a more interesting sum type" $
      exportsAs (Proxy @(Response String)) "test/IOTS/response.ts"
    it "Should export a function with tuples." $ do
      let someFunction :: (CurrencySymbol, TokenName) -> String
          someFunction _ = "Anything."
      exportsAs
        (Tagged @"tupleFunction" someFunction)
        "test/IOTS/functionTuple.ts"
    it "Should export a function with maybes." $ do
      let someFunction :: Maybe Slot -> String
          someFunction _ = "Anything."
      exportsAs
        (Tagged @"maybeFunction" someFunction)
        "test/IOTS/functionMaybe.ts"
    it "Should export a function with lists." $ do
      let someFunction :: [User] -> String
          someFunction _ = "Anything."
      exportsAs
        (Tagged @"listFunction" someFunction)
        "test/IOTS/functionList.ts"
    let functionA ::
             (CurrencySymbol, TokenName)
          -> Maybe Value
          -> Interval Slot
          -> [VestingTranche]
          -> String
        functionA _ _ _ _ = "Anything."
        functionB :: Interval Slot -> [CurrencySymbol] -> String
        functionB _ _ = "Anything."
    it "Should export a complex example" $ do
      exportsAs (Tagged @"functionA" functionA) "test/IOTS/vestingTranche.ts"
      exportsAs
        (HCons (Tagged @"functionA" functionA) HNil)
        "test/IOTS/vestingTranche.ts"
    it "Should export a mixed example" $
      exportsAs
        (HCons
           (Tagged @"functionA" functionA)
           (HCons (Tagged @"functionB" functionB) HNil))
        "test/IOTS/fullContract.ts"

exportsAs :: (IotsExportable a) => a -> FilePath -> IO ()
exportsAs exportable filename = do
  file <- Text.readFile =<< getDataFileName filename
  export exportable `shouldBePrettyDiff` file
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
  deriving (Show, Eq, Ord, Generic, IotsType)

data SimpleSum
  = This
  | That
  | TheOther
  deriving (Show, Eq, Ord, Generic, IotsType)

data User =
  User
    { userId :: Int
    , name   :: String
    }
  deriving (Show, Eq, Generic, IotsType)

data Response a
  = UnknownError Int Text
  | StatusError
      { code    :: Int
      , message :: Text
      , headers :: Map String Int
      }
  | EmptyResponse
  | Response a
  deriving (Show, Eq, Ord, Generic, IotsType)

newtype Slot =
  Slot
    { getSlot :: Integer
    }
  deriving (Show, Eq, Ord, Generic, IotsType)

newtype CurrencySymbol =
  CurrencySymbol
    { unCurrencySymbol :: Text
    }
  deriving (Show, Eq, Ord, Generic, IotsType)

newtype TokenName =
  TokenName
    { unTokenName :: Text
    }
  deriving (Show, Eq, Ord, Generic, IotsType)

newtype AssocMap k v =
  AssocMap
    { unMap :: [(k, v)]
    }
  deriving (Show, Eq, Ord, Generic, IotsType)

newtype Value =
  Value
    { getValue :: AssocMap CurrencySymbol (AssocMap TokenName Integer)
    }
  deriving (Show, Eq, Ord, Generic, IotsType)

data Interval a =
  Interval
    { ivFrom :: Maybe a
    , ivTo   :: Maybe a
    }
  deriving (Show, Eq, Ord, Generic, IotsType)

data VestingTranche =
  VestingTranche
    { vestingTrancheDate   :: Slot
    , vestingTrancheAmount :: Value
    , validity             :: Interval Slot
    }
  deriving (Show, Eq, Generic, IotsType)
