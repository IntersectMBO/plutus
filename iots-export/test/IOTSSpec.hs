{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE TypeApplications #-}

module IOTSSpec where

import           Data.ByteString.Lazy (ByteString, fromStrict)
import           Data.Map             (Map)
import           Data.Proxy           (Proxy (Proxy))
import           Data.Text            (Text)
import           Data.Text.Encoding   (encodeUtf8)
import           GHC.Generics         (Generic)
import           IOTS                 (HList (HCons, HNil), IotsExportable, IotsType, Tagged (Tagged), export)
import           Test.Tasty           (TestTree, testGroup)
import           Test.Tasty.Golden    (goldenVsString)

tests :: TestTree
tests =
    testGroup
        "Export to IOTS format"
        [ goldenVsString
              "Should export a single, fieldless constructor"
              "test/IOTS/singleFieldless.ts"
              (exportAs (Proxy @SingleFieldless))
        , goldenVsString
              "Should export a simple sum type"
              "test/IOTS/simpleSum.ts"
              (exportAs (Proxy @SimpleSum))
        , goldenVsString
              "Should export a sample user"
              "test/IOTS/user.ts"
              (exportAs (Proxy @User))
        , goldenVsString
              "Should export a more interesting sum type"
              "test/IOTS/response.ts"
              (exportAs (Proxy @(Response String)))
        , goldenVsString
              "Should export a function with tuples."
              "test/IOTS/functionTuple.ts"
              (let someFunction :: (CurrencySymbol, TokenName) -> String
                   someFunction _ = "Anything."
                in exportAs (Tagged @"tupleFunction" someFunction))
        , goldenVsString
              "Should export a function with maybes."
              "test/IOTS/functionMaybe.ts"
              (let someFunction :: Maybe Slot -> String
                   someFunction _ = "Anything."
                in exportAs (Tagged @"maybeFunction" someFunction))
        , goldenVsString
              "Should export a function with lists."
              "test/IOTS/functionList.ts"
              (let someFunction :: [User] -> String
                   someFunction _ = "Anything."
                in exportAs (Tagged @"listFunction" someFunction))
        , goldenVsString
              "Should export a complex example"
              "test/IOTS/vestingTranche.ts"
              (exportAs (Tagged @"functionA" functionA))
        , goldenVsString
              "Should export a complex example"
              "test/IOTS/vestingTranche.ts"
              (exportAs (HCons (Tagged @"functionA" functionA) HNil))
        , goldenVsString
              "Should export a mixed example"
              "test/IOTS/fullContract.ts"
              (exportAs
                   (HCons
                        (Tagged @"functionA" functionA)
                        (HCons (Tagged @"functionB" functionB) HNil)))
        ]
  where
    functionA ::
           (CurrencySymbol, TokenName)
        -> Maybe Value
        -> Interval Slot
        -> [VestingTranche]
        -> String
    functionA _ _ _ _ = "Anything."
    functionB :: Interval Slot -> [CurrencySymbol] -> String
    functionB _ _ = "Anything."

exportAs :: IotsExportable a => a -> IO ByteString
exportAs = pure . fromStrict . encodeUtf8 . export

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
