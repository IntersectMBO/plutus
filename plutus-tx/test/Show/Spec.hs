{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Show.Spec where

import PlutusTx.Bool
import PlutusTx.Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Show

import Control.Monad.Reader as Reader
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Char8 qualified as Char8
import Data.Text qualified as Text
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude hiding (Show (..))
import System.FilePath
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.Hedgehog

toHaskellString :: BuiltinString -> String
toHaskellString (BI.BuiltinString t) = Text.unpack t

showIntegerRoundtrip :: Property
showIntegerRoundtrip = property $ do
  integer :: Integer <- forAll $ Gen.integral (Range.linear (-10000) 10000)
  read (toHaskellString (show integer)) === integer

showByteStringBase16 :: Property
showByteStringBase16 = property $ do
  bytestring <- forAll $ Gen.bytes (Range.linear 0 20)
  let hex = Base16.encode bytestring
      builtinBytestring = BI.BuiltinByteString bytestring
  toHaskellString (show builtinBytestring) === Char8.unpack hex

goldenShow :: forall a. (Show a) => TestName -> a -> TestNested
goldenShow name x = do
  path <- ask
  let fp = foldr (</>) (name ++ ".golden.show") path
  embed $ goldenVsText name fp . fromBuiltin $ show x

data ProductD = ProductC Integer [Bool]
deriveShow ''ProductD

data ProductD2 = (:-:) [Integer] Bool
deriveShow ''ProductD2

data SumD = SumC1 | SumC2 (Integer, BuiltinString, BuiltinByteString)
deriveShow ''SumD

data RecordD = RecordC {field1 :: BuiltinString, field2 :: ([Integer], Bool)}
deriveShow ''RecordD

data InfixD = (Integer, Bool) :+: [BuiltinString]
deriveShow ''InfixD

data InfixD2 = (Integer, Bool) `InfixC` BuiltinString
deriveShow ''InfixD2

data PolyD a b = PolyC (a, b) [(a, b)]
deriveShow ''PolyD

data GadtD a where
  GadtC :: Integer -> BuiltinString -> GadtD Bool
deriveShow ''GadtD

propertyTests :: TestTree
propertyTests =
  testGroup
    "PlutusTx.Show property-based tests"
    [ testPropertyNamed
        "PlutusTx.Show @Integer"
        "PlutusTx.Show @Integer"
        showIntegerRoundtrip
    , testPropertyNamed
        "PlutusTx.Show @BuiltinByteString"
        "PlutusTx.Show @BuiltinByteString"
        showByteStringBase16
    ]

goldenTests :: TestTree
goldenTests =
  runTestNested
    ["test", "Show", "Golden"]
    [ goldenShow "product-type" (ProductC 3 [True, False])
    , goldenShow "product-type-2" ((:-:) [-300] False)
    , goldenShow "sum-type-1" SumC1
    , goldenShow "sum-type-2" (SumC2 (1, "string", "bytestring"))
    , goldenShow "record-type" (RecordC "string" ([0, 1, 2, 3], True))
    , goldenShow "infix-type" ((42, True) :+: ["foo", "bar"])
    , goldenShow "infix-type-2" ((-12345, True) `InfixC` "foo")
    , goldenShow "gadt" (GadtC (-42) "string")
    , goldenShow "poly" (PolyC (42 :: Integer, False) [])
    ]
