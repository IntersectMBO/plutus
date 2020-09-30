{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
module Main(main) where

import           Control.Lens
import           Control.Monad              (void)
import           Control.Monad.Trans.Except (runExcept)
import qualified Data.Aeson                 as JSON
import qualified Data.Aeson.Extras          as JSON
import qualified Data.Aeson.Internal        as Aeson
import qualified Data.ByteString            as BSS
import qualified Data.ByteString.Lazy       as BSL
import           Data.Either                (isLeft, isRight)
import           Data.Foldable              (fold, foldl', traverse_)
import           Data.List                  (sort)
import qualified Data.Map                   as Map
import           Data.Monoid                (Sum (..))
import qualified Data.Set                   as Set
import           Data.String                (IsString (fromString))
import           Hedgehog                   (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen               as Gen
import qualified Hedgehog.Range             as Range
import qualified Language.PlutusTx.AssocMap as AssocMap
import qualified Language.PlutusTx.Builtins as Builtins
import qualified Language.PlutusTx.Prelude  as PlutusTx
import           Ledger
import qualified Ledger.Ada                 as Ada
import qualified Ledger.Generators          as Gen
import qualified Ledger.Index               as Index
import qualified Ledger.Interval            as Interval
import           Ledger.Value               (CurrencySymbol, Value (Value))
import qualified Ledger.Value               as Value
import           LedgerBytes
import           Test.Tasty
import           Test.Tasty.Hedgehog        (testProperty)
import           Test.Tasty.HUnit           (testCase)
import qualified Test.Tasty.HUnit           as HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "all tests" [
    testGroup "UTXO model" [
        testProperty "initial transaction is valid" initialTxnValid
        ],
    testGroup "intervals" [
        testProperty "member" intvlMember,
        testProperty "contains" intvlContains
        ],
    testGroup "values" [
        testProperty "additive identity" valueAddIdentity,
        testProperty "additive inverse" valueAddInverse,
        testProperty "scalar identity" valueScalarIdentity,
        testProperty "scalar distributivity" valueScalarDistrib
        ],
    testGroup "Etc." [
        testProperty "splitVal" splitVal,
        testProperty "encodeByteString" encodeByteStringTest,
        testProperty "encodeSerialise" encodeSerialiseTest
        ],
    testGroup "LedgerBytes" [
        testProperty "show-fromHex" ledgerBytesShowFromHexProp,
        testProperty "toJSON-fromJSON" ledgerBytesToJSONProp
        ],
    testGroup "Value" ([
        testProperty "Value ToJSON/FromJSON" (jsonRoundTrip Gen.genValue),
        testProperty "CurrencySymbol ToJSON/FromJSON" (jsonRoundTrip $ Value.currencySymbol <$> Gen.genSizedByteStringExact 32),
        testProperty "TokenName ToJSON/FromJSON" (jsonRoundTrip Gen.genTokenName),
        testProperty "CurrencySymbol IsString/Show" currencySymbolIsStringShow
        ] ++ (let   vlJson :: BSL.ByteString
                    vlJson = "{\"getValue\":[[{\"unCurrencySymbol\":\"ab01ff\"},[[{\"unTokenName\":\"myToken\"},50]]]]}"
                    vlValue = Value.singleton "ab01ff" "myToken" 50
                in byteStringJson vlJson vlValue)
          ++ (let   vlJson :: BSL.ByteString
                    vlJson = "{\"getValue\":[[{\"unCurrencySymbol\":\"\"},[[{\"unTokenName\":\"\"},50]]]]}"
                    vlValue = Ada.lovelaceValueOf 50
                in byteStringJson vlJson vlValue))
    ]

initialTxnValid :: Property
initialTxnValid = property $ do
    (i, _) <- forAll . pure $ Gen.genInitialTransaction Gen.generatorModel
    Gen.assertValid i Gen.emptyChain

splitVal :: Property
splitVal = property $ do
    i <- forAll $ Gen.integral $ Range.linear 1 (100000 :: Integer)
    n <- forAll $ Gen.integral $ Range.linear 1 100
    vs <- forAll $ Gen.splitVal n i
    Hedgehog.assert $ sum vs == i
    Hedgehog.assert $ length vs <= n

valueAddIdentity :: Property
valueAddIdentity = property $ do
    vl1 <- forAll Gen.genValue
    Hedgehog.assert $ vl1 == (vl1 PlutusTx.+ PlutusTx.zero)
    Hedgehog.assert $ vl1 == (PlutusTx.zero PlutusTx.+ vl1)

valueAddInverse :: Property
valueAddInverse = property $ do
    vl1 <- forAll Gen.genValue
    let vl1' = PlutusTx.negate vl1
    Hedgehog.assert $ PlutusTx.zero == (vl1 PlutusTx.+ vl1')

valueScalarIdentity :: Property
valueScalarIdentity = property $ do
    vl1 <- forAll Gen.genValue
    Hedgehog.assert $ vl1 == PlutusTx.scale 1 vl1

valueScalarDistrib :: Property
valueScalarDistrib = property $ do
    vl1 <- forAll Gen.genValue
    vl2 <- forAll Gen.genValue
    scalar <- forAll (Gen.integral (fromIntegral <$> Range.linearBounded @Int))
    let r1 = PlutusTx.scale scalar (vl1 PlutusTx.+ vl2)
        r2 = PlutusTx.scale scalar vl1 PlutusTx.+ PlutusTx.scale scalar vl2
    Hedgehog.assert $ r1 == r2

intvlMember :: Property
intvlMember = property $ do
    (i1, i2) <- forAll $ (,) <$> Gen.integral (fromIntegral <$> Range.linearBounded @Int) <*> Gen.integral (fromIntegral <$> Range.linearBounded @Int)
    let (from, to) = (min i1 i2, max i1 i2)
        i          = Interval.interval (Slot from) (Slot to)
    Hedgehog.assert $ Interval.member (Slot from) i || Interval.isEmpty i
    Hedgehog.assert $ not (Interval.member (Slot (from-1)) i) || Interval.isEmpty i
    Hedgehog.assert $ Interval.member (Slot to) i || Interval.isEmpty i
    Hedgehog.assert $ not (Interval.member (Slot (to+1)) i) || Interval.isEmpty i

intvlContains :: Property
intvlContains = property $ do
    -- generate two intervals from a sorted list of ints
    -- the outer interval contains the inner interval
    ints <- forAll $ traverse (const $ Gen.integral (fromIntegral <$> Range.linearBounded @Int)) [1..4]
    let [i1, i2, i3, i4] = Slot <$> sort ints
        outer = Interval.interval i1 i4
        inner = Interval.interval i2 i3

    Hedgehog.assert $ Interval.contains outer inner

encodeByteStringTest :: Property
encodeByteStringTest = property $ do
    bs <- forAll $ Gen.bytes $ Range.linear 0 1000
    let enc    = JSON.String $ JSON.encodeByteString bs
        result = Aeson.iparse JSON.decodeByteString enc

    Hedgehog.assert $ result == Aeson.ISuccess bs

encodeSerialiseTest :: Property
encodeSerialiseTest = property $ do
    txt <- forAll $ Gen.text (Range.linear 0 1000) Gen.unicode
    let enc    = JSON.String $ JSON.encodeSerialise txt
        result = Aeson.iparse JSON.decodeSerialise enc

    Hedgehog.assert $ result == Aeson.ISuccess txt

jsonRoundTrip :: (Show a, Eq a, JSON.FromJSON a, JSON.ToJSON a) => Hedgehog.Gen a -> Property
jsonRoundTrip gen = property $ do
    bts <- forAll gen
    let enc    = JSON.toJSON bts
        result = Aeson.iparse JSON.parseJSON enc

    Hedgehog.assert $ result == Aeson.ISuccess bts

ledgerBytesShowFromHexProp :: Property
ledgerBytesShowFromHexProp = property $ do
    bts <- forAll $ LedgerBytes <$> Gen.genSizedByteString 32
    let result = LedgerBytes.fromHex $ fromString $ show bts

    Hedgehog.assert $ result == Right bts

ledgerBytesToJSONProp :: Property
ledgerBytesToJSONProp = property $ do
    bts <- forAll $ LedgerBytes <$> Gen.genSizedByteString 32
    let enc    = JSON.toJSON bts
        result = Aeson.iparse JSON.parseJSON enc

    Hedgehog.assert $ result == Aeson.ISuccess bts

currencySymbolIsStringShow :: Property
currencySymbolIsStringShow = property $ do
    cs <- forAll $ Value.currencySymbol <$> Gen.genSizedByteStringExact 32
    let cs' = fromString (show cs)
    Hedgehog.assert $ cs' == cs

-- byteStringJson :: (Eq a, JSON.FromJSON a) => BSL.ByteString -> a -> [TestCase]
byteStringJson jsonString value =
    [ testCase "decoding" $
        HUnit.assertEqual "Simple Decode" (Right value) (JSON.eitherDecode jsonString)
    , testCase "encoding" $ HUnit.assertEqual "Simple Encode" jsonString (JSON.encode value)
    ]
