{-# LANGUAGE TypeApplications #-}
module Main(main) where

import qualified Codec.CBOR.FlatTerm    as FlatTerm
import           Codec.Serialise        (deserialiseOrFail, serialise)
import qualified Codec.Serialise        as Serialise
import           Hedgehog               (MonadGen, Property, annotateShow, assert, forAll, property)
import qualified Hedgehog.Gen           as Gen
import qualified Hedgehog.Range         as Range
import           Language.PlutusTx.Data (Data (..))
import           Test.Tasty
import           Test.Tasty.Hedgehog    (testProperty)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutus-tx" [
    serdeTests
    ]

serdeTests :: TestTree
serdeTests = testGroup "Data serialisation"
    [ testProperty "data round-trip" dataRoundTrip
    ]

dataRoundTrip :: Property
dataRoundTrip = property $ do
    dt :: Data <- forAll genData
    let res = deserialiseOrFail (serialise dt)
    annotateShow res

    -- Debugging info
    let ft = FlatTerm.toFlatTerm $ Serialise.encode dt
    annotateShow ft
    annotateShow $ FlatTerm.validFlatTerm ft
    assert (res == Right dt)

genData :: MonadGen m => m Data
genData =
    let st = Gen.subterm genData id
        positiveInteger = Gen.integral (Range.linear 0 100000)
        constructorArgList = Gen.list (Range.linear 0 50) st
        kvMapList = Gen.list (Range.linear 0 50) ((,) <$> st <*> st)
    in
    Gen.recursive Gen.choice
        [ I <$> Gen.integral (Range.linear (-100000) 100000)
        , B <$> Gen.bytes (Range.linear 0 1000) ]
        [ Constr <$> positiveInteger <*> constructorArgList
        , List <$> constructorArgList
        , Map <$> kvMapList
        ]
