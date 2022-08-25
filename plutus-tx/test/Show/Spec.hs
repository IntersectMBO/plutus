-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Show.Spec where

import PlutusTx.Bool
import PlutusTx.Builtins
import PlutusTx.Show

import Control.Monad.Trans.Reader as Reader
import Prelude hiding (Show (..))
import System.FilePath
import Test.Tasty
import Test.Tasty.Extras

goldenShow :: forall a. Show a => TestName -> a -> TestNested
goldenShow name x = do
    path <- ask
    let fp = foldr (</>) (name ++ ".show.golden") path
    pure $ goldenVsText name fp . fromBuiltin $ show x

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

tests :: TestNested
tests =
    testNested
        "Show"
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
