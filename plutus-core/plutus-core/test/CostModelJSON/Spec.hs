{-| Tests pinning the serialized JSON of the cost model types.

The field names, constructor tags and structure of 'BuiltinCostModelBase' and
'CekMachineCostsBase' are a frozen format: the serialized form has to match the checked-in
@cost-model/data/*.json@ files, and the flattened keys become the ledger's cost model
parameter names. Renaming any of them is an observable breakage rather than an implementation
detail.

Those data files are the frozen format, so they are used as the expected output directly and
no second copy is needed. Comparing against them catches renamed fields, renamed constructor
tags, and fields appearing or disappearing.

Note that the models under test are themselves loaded from those files by Template Haskell, so
this is a fixed-point check on the encoder rather than a check on the cost model numbers: a
changed coefficient moves both sides together. Anything that breaks decoding already fails the
build at that splice, which leaves the case where 'toJSON' alone drifts away from 'parseJSON' —
possible because the two are written out separately.

Everything is compared as 'Data.Aeson.Value's. Field order carries no meaning here: every
consumer either parses the JSON or goes through 'CostModelParams', which is a sorted map. -}
module CostModelJSON.Spec (test_costModelJSON) where

import PlutusCore.DataFilePaths qualified as DFP
import PlutusCore.Default (BuiltinSemanticsVariant (..), DefaultFun)
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (cekCostModelForVariant)
import PlutusCore.Evaluation.Machine.MachineParameters
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts

import Barbies (bmap)
import Data.Aeson qualified as Aeson
import Data.Aeson.Diff qualified as Diff
import Data.Aeson.Encode.Pretty qualified as AesonPretty
import Data.ByteString.Lazy.Char8 qualified as BSL8
import Data.Functor.Identity (runIdentity)
import Test.Tasty
import Test.Tasty.HUnit

-- | Every semantics variant, with the data files holding its frozen cost model.
variants :: [(String, BuiltinSemanticsVariant DefaultFun, FilePath, FilePath)]
variants =
  [ ("A", DefaultFunSemanticsVariantA, DFP.builtinCostModelFileA, DFP.cekMachineCostsFileA)
  , ("B", DefaultFunSemanticsVariantB, DFP.builtinCostModelFileB, DFP.cekMachineCostsFileB)
  , ("C", DefaultFunSemanticsVariantC, DFP.builtinCostModelFileC, DFP.cekMachineCostsFileC)
  , ("D", DefaultFunSemanticsVariantD, DFP.builtinCostModelFileD, DFP.cekMachineCostsFileD)
  , ("E", DefaultFunSemanticsVariantE, DFP.builtinCostModelFileE, DFP.cekMachineCostsFileE)
  ]

{-| Assert that @model@ serializes to exactly the JSON stored in @file@. On a mismatch the
difference is reported as a JSON patch, which pinpoints the offending entries instead of
printing both cost models in full. -}
assertMatchesDataFile :: Aeson.ToJSON a => FilePath -> a -> Assertion
assertMatchesDataFile file model = do
  contents <- BSL8.readFile file
  case Aeson.eitherDecode contents of
    Left err -> assertFailure $ file ++ ": " ++ err
    Right stored ->
      assertEqualWithPatch ("serialized form no longer matches " ++ file) stored (Aeson.toJSON model)

{-| Compare two JSON values, describing any difference as the JSON patch that turns the first
into the second. -}
assertEqualWithPatch :: String -> Aeson.Value -> Aeson.Value -> Assertion
assertEqualWithPatch what expected actual
  | expected == actual = pure ()
  | otherwise =
      assertFailure . unlines $
        [ what
        , "patch from the expected value to the actual one:"
        , BSL8.unpack (AesonPretty.encodePretty (Diff.diff expected actual))
        ]

test_costModelJSON :: TestTree
test_costModelJSON =
  testGroup
    "cost model JSON encoding stability"
    [ testGroup
        "toJSON matches the checked-in cost model data file"
        [ testGroup
            variantName
            [ testCase "builtinCostModel" $
                assertMatchesDataFile builtinFile (_builtinCostModel costModel)
            , testCase "cekMachineCosts" $
                assertMatchesDataFile cekFile (_machineCostModel costModel)
            ]
        | (variantName, variant, builtinFile, cekFile) <- variants
        , let costModel = cekCostModelForVariant variant
        ]
    , testGroup
        "field-omitting instances"
        [ testCase "CekMachineCostsBase Maybe: all fields missing encodes to {}" $
            assertEqualWithPatch
              "unset machine costs were not omitted"
              (Aeson.object [])
              (Aeson.toJSON (bmap (const Nothing) cekMachineCostsA :: CekMachineCostsBase Maybe))
        , testCase "BuiltinCostModelBase MCostingFun: all fields missing encodes to {}" $
            assertEqualWithPatch
              "unset costing functions were not omitted"
              (Aeson.object [])
              ( Aeson.toJSON
                  ( bmap (const (MCostingFun Nothing)) builtinCostModelA
                      :: BuiltinCostModelBase MCostingFun
                  )
              )
        , testCase "CekMachineCostsBase Maybe: all fields present encodes as the base instance" $
            assertEqualWithPatch
              "fully populated machine costs differ from the base instance"
              (Aeson.toJSON cekMachineCostsA)
              (Aeson.toJSON (bmap (Just . runIdentity) cekMachineCostsA))
        , testCase "BuiltinCostModelBase MCostingFun: all present encodes as the base instance" $
            assertEqualWithPatch
              "fully populated costing functions differ from the base instance"
              (Aeson.toJSON builtinCostModelA)
              (Aeson.toJSON (bmap (MCostingFun . Just) builtinCostModelA))
        ]
    ]
  where
    builtinCostModelA = _builtinCostModel (cekCostModelForVariant DefaultFunSemanticsVariantA)
    cekMachineCostsA = _machineCostModel (cekCostModelForVariant DefaultFunSemanticsVariantA)
