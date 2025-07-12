-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.Versions (tests) where

import PlutusCore as PLC
import PlutusCore.Data as PLC
import PlutusCore.MkPlc as PLC
import PlutusCore.Version as PLC
import PlutusLedgerApi.Common
import PlutusLedgerApi.Common.Versions
import PlutusPrelude
import UntypedPlutusCore as UPLC

import PlutusLedgerApi.Test.Scripts
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3

import Data.ByteString qualified as BS
import Data.ByteString.Short qualified as BSS
import Data.Either
import Data.List (intercalate, (\\))
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Vector.Strict (Vector, fromList)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

tests :: TestTree
tests = testGroup "versions"
    [ testLedgerLanguages
    , testBuiltinVersions2
    , testBuiltinsAvailableIn
    , testLanguageVersions
    , testRmdr
    ]

testLedgerLanguages :: TestTree
testLedgerLanguages = testGroup "ledger languages"
    [ testProperty "v1 not before but after" $ prop_notBeforeButAfter V1.deserialiseScript alonzoPV
    , testProperty "v2 not before but after" $ prop_notBeforeButAfter V2.deserialiseScript vasilPV
    , testProperty "v3 not before but after" $ prop_notBeforeButAfter V3.deserialiseScript changPV
    , testProperty "protocol-versions can add but not remove ledger languages" $
        \pvA pvB -> pvA < pvB ==> ledgerLanguagesAvailableIn pvA `Set.isSubsetOf` ledgerLanguagesAvailableIn pvB
    ]
  where
    prop_notBeforeButAfter :: (MajorProtocolVersion -> SerialisedScript -> Either ScriptDecodeError b)
                           -> MajorProtocolVersion -> MajorProtocolVersion -> Bool
    prop_notBeforeButAfter phase1Func expectedPv genPv =
        -- run phase 1 on an example script
        let resPhase1 = phase1Func genPv errorScript
        in if genPv < expectedPv
           -- generated an old protocol version
           then
               case resPhase1 of
                   Left LedgerLanguageNotAvailableError{} -> True
                   _                                      -> False
           -- generated an eq or gt the expected protocol version
           else isRight resPhase1

deriving newtype instance Arbitrary MajorProtocolVersion

-- ** FIXME: should we extend this???
testBuiltinVersions :: TestTree
testBuiltinVersions = testGroup "builtins"
    [ {- testCase "all builtins are eventually available in all ledger languages" $
      let builtinsFor ll = fold $ Map.elems $ fold $ fmap builtinsIntroducedIn enumerate
          allBuiltins = enumerate @DefaultFun
      in for_ allBuiltins $ \f -> assertBool (show f) (f `Set.member` allPvBuiltins)
    , -} testCase "PlutusV1 builtins aren't available before Alonzo" $
        assertBool "empty" (Set.null $ builtinsAvailableIn PlutusV1 maryPV)
    , testCase "PlutusV2  builtins aren't available before Vasil" $
        assertBool "empty" (Set.null $ builtinsAvailableIn PlutusV2 alonzoPV)
    , testCase "PlutusV3  builtins aren't available before Chang" $
        assertBool "empty" (Set.null $ builtinsAvailableIn PlutusV3 valentinePV)
    , testCase "serializeData is only available in V2 and V3 Vasil and after" $ do
        assertBool "in V1 @Alonzo"     $ isLeft  $ V1.deserialiseScript alonzoPV serialiseDataExScript
        assertBool "in V1 @Vasil"      $ isLeft  $ V1.deserialiseScript vasilPV  serialiseDataExScript
        assertBool "in V2 @Alonzo"     $ isLeft  $ V2.deserialiseScript alonzoPV serialiseDataExScript
        assertBool "in V3 @Alonzo"     $ isLeft  $ V3.deserialiseScript alonzoPV serialiseDataExScript
        assertBool "not in V2 @Vasil"  $ isRight $ V2.deserialiseScript vasilPV  serialiseDataExScript
        assertBool "not in V3 @future" $ isRight $ V3.deserialiseScript futurePV serialiseDataExScript
    , testCase "bls,keccak256,blake2b224 only available in V3, Chang and after" $
         for_ [blsG1AddExScript, blsFinalVerifyExScript, keccak256ExScript, blake2b224ExScript] $ \script -> do
             assertBool "in V1 @Alonzo"      $ isLeft  $ V1.deserialiseScript alonzoPV    script
             assertBool "in V1 @Vasil"       $ isLeft  $ V1.deserialiseScript vasilPV     script
             assertBool "in V2 @Alonzo"      $ isLeft  $ V2.deserialiseScript alonzoPV    script
             assertBool "in V3 @Alonzo"      $ isLeft  $ V3.deserialiseScript alonzoPV    script
             assertBool "in V2 @Valentine"   $ isLeft  $ V2.deserialiseScript valentinePV script
             assertBool "in V2 @Valentine"   $ isLeft  $ V2.deserialiseScript valentinePV script
             assertBool "not in V3 @future"  $ isRight $ V3.deserialiseScript futurePV    script
    ]

showPV :: MajorProtocolVersion -> String
showPV (MajorProtocolVersion pv) =
  case pv of
    2  -> "Shelley (PV2)"
    3  -> "Allegra (PV3)"
    4  -> "Mary (PV4)"
    5  -> "Alonzo (PV5)"
    7  -> "Vasil (PV7)"
    8  -> "Valentine (PV8)"
    9  -> "Chang (PV9)"
    10 -> "Plomin (PV10)"
    11 -> "Anon (PV11)"
    _  -> "<unknown> (PV" ++ show pv ++ ")"

-- Should we test plcVersion110 as well?
mkScript :: DefaultFun -> (String, SerialisedScript)
mkScript fun =
  (show fun, serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ builtin () fun)

builtins1 :: [(String, SerialisedScript)]
builtins1 = fmap mkScript batch1

builtins2 :: [(String, SerialisedScript)]
builtins2 = fmap mkScript batch2

builtins3 :: [(String, SerialisedScript)]
builtins3 = fmap mkScript batch3

builtins4a :: [(String, SerialisedScript)]
builtins4a = fmap mkScript batch4a

builtins4b :: [(String, SerialisedScript)]
builtins4b = fmap mkScript batch4b

builtins5 :: [(String, SerialisedScript)]
builtins5 = fmap mkScript batch5

builtins6 :: [(String, SerialisedScript)]
builtins6 = fmap mkScript batch6

allBuiltins :: [(String, SerialisedScript)]
allBuiltins = builtins1 ++ builtins2
             ++ builtins3 ++ builtins4a
             ++ builtins4b ++ builtins5
             ++ builtins6

-- | Test that the builtins that we expect to be allowed in each LL/PV
-- combination can be successfully deserialised and that the rest cannot.  This
-- is mostly testing that `builtinsAvailableIn` does what it's supposed to.
-- This should be updated when new builtins, ledger languages, or protocol
-- versions are added, but we expect that after Anon all builtins will be
-- allowed in all ledger languages.
testBuiltinVersions2 :: TestTree
testBuiltinVersions2 =
  let testBuiltins ll deserialise pv expectedGood =
        let expectGood scripts =
              for_ scripts $ \(name, script) ->
              assertBool  (name ++ " not allowed in " ++ show ll ++" @" ++ showPV pv) $
              isRight $ deserialise pv script
            expectBad scripts =
              for_ scripts $ \(name, script) ->
              assertBool  (name ++ " should be allowed in " ++ show ll ++" @" ++ showPV pv) $
              isLeft $ deserialise pv script
        in testCase (showPV pv) $ do
          expectGood expectedGood
          expectBad (allBuiltins \\ expectedGood)
  in  testGroup "Builtins allowed"
  [ let mkTest = testBuiltins PlutusV1 V1.deserialiseScript
    in testGroup "PlutusV1"
         [ mkTest shelleyPV   []
         , mkTest allegraPV   []
         , mkTest maryPV      []
         , mkTest alonzoPV    builtins1
         , mkTest vasilPV     builtins1
         , mkTest valentinePV builtins1
         , mkTest changPV     builtins1
         , mkTest plominPV    builtins1
         , mkTest anonPV      allBuiltins
      ]
    , let mkTest = testBuiltins PlutusV2 V2.deserialiseScript
      in testGroup "PlutusV2"
         [ mkTest shelleyPV   []
         , mkTest allegraPV   []
         , mkTest maryPV      []
         , mkTest alonzoPV    []
         , mkTest vasilPV     (builtins1 ++ builtins2)
         , mkTest valentinePV (builtins1 ++ builtins2 ++ builtins3)
         , mkTest changPV     (builtins1 ++ builtins2 ++ builtins3)
         , mkTest plominPV    (builtins1 ++ builtins2 ++ builtins3 ++ builtins4b)
         , mkTest anonPV      allBuiltins
      ]
    , let mkTest = testBuiltins PlutusV3 V3.deserialiseScript
      in testGroup "PlutusV3"
         [ mkTest shelleyPV   []
         , mkTest allegraPV   []
         , mkTest maryPV      []
         , mkTest alonzoPV    []
         , mkTest vasilPV     []
         , mkTest valentinePV []
         , mkTest changPV     (builtins1 ++ builtins2 ++ builtins3 ++ builtins4a ++ builtins4b)
         , mkTest plominPV    (builtins1 ++ builtins2 ++ builtins3 ++ builtins4a ++ builtins4b ++ builtins5)
         , mkTest anonPV      allBuiltins
      ]
    ]

-- Check that the `builtinsAvailableIn` function returns the correct number of
-- buitins for each LL and PV (but not that it returns the _correct_ builtins).
-- The `builtinCounts` function MUST be updated whenever `builtinsAvailableIn`
-- is updated, which will usually happen in the run-up to the introduction of a
-- new LL or PV.
testBuiltinsAvailableIn :: TestTree
testBuiltinsAvailableIn =
  let builtinCounts :: PlutusLedgerLanguage -> [(MajorProtocolVersion, Int)]
      builtinCounts = \case
        PlutusV1 -> [ (shelleyPV, 0)
                    , (allegraPV, 0)
                    , (maryPV, 0)
                    , (alonzoPV, 51)    -- Batch 1
                    , (vasilPV, 51)
                    , (valentinePV, 51)
                    , (changPV, 51)
                    , (plominPV, 51)
                    , (anonPV, 92)      -- Batches 2-6
                    ]
        PlutusV2 -> [ (shelleyPV, 0)
                    , (allegraPV, 0)
                    , (maryPV, 0)
                    , (alonzoPV, 0)
                    , (vasilPV, 52)     -- Batches 1 and 2
                    , (valentinePV, 54) -- Batch 3
                    , (changPV, 54)
                    , (plominPV, 56)    -- Batch 4a
                    , (anonPV, 92)      -- Batches 4b-6
                    ]
        PlutusV3 -> [ (shelleyPV, 0)
                    , (allegraPV, 0)
                    , (maryPV, 0)
                    , (alonzoPV, 0)
                    , (vasilPV, 0)
                    , (valentinePV, 0)
                    , (changPV, 75)     -- Batches 1-4
                    , (plominPV, 87)    -- Batch 5
                    , (anonPV, 92)      -- Batch 6
                    ]
      allKnownLLs = enumerate @PlutusLedgerLanguage
      numKnownPVs = length knownPVs
      mkTestsFor ll =
        testGroup ("Number of builtins for " ++ show ll) $
        checkPVcount ll : fmap (mkTest ll) (builtinCounts ll)
      checkPVcount ll =
        testCase "Test covers all known protocol versions" $
        (assertBool ("Wrong number of PVs for " ++ show ll) $ length (builtinCounts ll) == numKnownPVs)
      mkTest ll (pv, expected) =
        let actual = length $ builtinsAvailableIn ll pv
        in testCase ("PV" ++ show pv ++ ": " ++ show expected ++ " builtins expected") $
           assertBool ("Expected " ++ show expected ++ " builtins, found " ++ show actual) $ actual == expected
  in testGroup "builtinsAvailableIn returns correct number of builtins" $ fmap mkTestsFor allKnownLLs

testRmdr :: TestTree
testRmdr = testGroup "extra bytes at end of script"
    [ testCase "remdr" $ do
         assertBool "remdr1" $ isRight $ V1.deserialiseScript valentinePV $ errorScript <> "remdr1"
         assertBool "remdr2" $ isRight $ V2.deserialiseScript valentinePV $ errorScript <> "remdr2"
         assertBool "remdr1c" $ isRight $ V1.deserialiseScript changPV $ errorScript <> "remdr1"
         assertBool "remdr2c" $ isRight $ V2.deserialiseScript changPV $ errorScript <> "remdr2"
         assertEqual "remdr3" (RemainderError "remdr3") $ fromLeft (Prelude.error "Expected Reft, got Right") $ V3.deserialiseScript changPV $ errorScript <> "remdr3"
    , testProperty "remdr1gen"$ \remdr -> isRight $ V1.deserialiseScript valentinePV $ errorScript <> BSS.pack remdr
    , testProperty "remdr2gen"$ \remdr -> isRight $ V2.deserialiseScript valentinePV $ errorScript <> BSS.pack remdr
    , testProperty "remdr1genc"$ \remdr -> isRight $ V1.deserialiseScript changPV $ errorScript <> BSS.pack remdr
    , testProperty "remdr2genc"$ \remdr -> isRight $ V2.deserialiseScript changPV $ errorScript <> BSS.pack remdr
    -- we cannot make the same property as above for remdr3gen because it may generate valid bytestring append extensions to the original script
    -- a more sophisticated one could work though
    ]

-- See Note [Checking the Plutus Core language version] for why these have to use mkTermToEvaluate
testLanguageVersions :: TestTree
testLanguageVersions = testGroup "Plutus Core language versions"
  [ testCase "v1.1.0 is available in l3,Chang and not before" $ do
      -- `LedgerLanguageNotAvailableError` is checked in `deserialiseScript`
      assertBool "in l3,Vasil" $ isLeft $ uplcToScriptForEvaluation PlutusV3 vasilPV v110script
      -- `PlutusCoreLanguageNotAvailableError` is checked in `mkTermToEvaluate`
      assertBool "in l2,Chang" $ isLeft $ mkTermToEvaluate PlutusV2 changPV (either (Prelude.error . show) id (V2.deserialiseScript changPV $ serialiseUPLC v110script)) []
      -- Both `deserialiseScript` and `mkTermToEvaluate` should succeed
      assertBool "not in l3,Chang" $ isRight $ mkTermToEvaluate PlutusV3 changPV (either (Prelude.error . show) id (V3.deserialiseScript changPV $ serialiseUPLC v110script)) []
    -- The availability of `case` and `constr` is checked in `deserialise`
  , testCase "constr is not available with v1.0.0 ever" $ assertBool "in l3,future" $ isLeft $ uplcToScriptForEvaluation PlutusV3 changPV badConstrScript
  , testCase "case is not available with v1.0.0 ever" $ assertBool "in l3,future" $ isLeft $ uplcToScriptForEvaluation PlutusV3 changPV badCaseScript
  ]

-- * UPLC written examples to test builtin deserialisation

-- First builtin in Batch 1
addIntegerExScript :: SerialisedScript
addIntegerExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
   builtin () AddInteger @@ [ mkConstant @Integer () 111, mkConstant @Integer () 222 ]

-- Last builtin in Batch 1
mkNilPairDataExScript :: SerialisedScript
mkNilPairDataExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () MkNilPairData @@ [ mkConstant () () ]

batch1ExScripts :: [(String, SerialisedScript)]
batch1ExScripts = [ ("addInteger", addIntegerExScript)
                  , ("mkNilPairData", mkNilPairDataExScript)]

-- Only builtin in Batch 2
serialiseDataExScript :: SerialisedScript
serialiseDataExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    builtin () SerialiseData @@ [ mkConstant () $ I 1 ]

batch2ExScripts :: [(String, SerialisedScript)]
batch2ExScripts = [("serialiseData", serialiseDataExScript)]

-- Batch 3

verifyEcdsaSecp256k1SignatureExScript :: SerialisedScript
verifyEcdsaSecp256k1SignatureExScript =
  serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    builtin () VerifyEcdsaSecp256k1Signature

verifySchnorrSecp256k1SignatureExScript :: SerialisedScript
verifySchnorrSecp256k1SignatureExScript =
  serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    builtin () VerifyEcdsaSecp256k1Signature

batch3ExScripts :: [(String, SerialisedScript)]
batch3ExScripts = [ ("verifyEcdsaSecp256k1Signature", verifyEcdsaSecp256k1SignatureExScript)
                  , ("verifySchnorrSecp256k1Signature", verifySchnorrSecp256k1SignatureExScript) ]

-- Batch 4a
-- Note that these can work also with plcversion==1.1.0

-- First BLS12_381 function
-- It'd be quite complicated to apply it,  but we're only testing deserialisation.
blsG1AddExScript :: SerialisedScript
blsG1AddExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () Bls12_381_G1_add

-- Final BLS12_381 function
-- It'd be quite complicated to apply it,  but we're only testing deserialisation.
blsFinalVerifyExScript :: SerialisedScript
blsFinalVerifyExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () Bls12_381_finalVerify

-- Note that keccak can work also with plcversion==1.1.0
keccak256ExScript :: SerialisedScript
keccak256ExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () Keccak_256 @@ [ mkConstant @BS.ByteString () "hashme" ]

-- Note that blake2b224 can work also with plcversion==1.1.0
blake2b224ExScript :: SerialisedScript
blake2b224ExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () Blake2b_224 @@ [ mkConstant @BS.ByteString () "hashme" ]

batch4aExScripts :: [(String, SerialisedScript)]
batch4aExScripts = [ ("bls12_381_G1_add", blsG1AddExScript)
                   , ("bls12_381_finalVerify", blsFinalVerifyExScript)
                   , ("keccak_256", keccak256ExScript)
                   , ("blake2b_224", blake2b224ExScript) ]


-- Batch 4a (enabled in Vasil with Batch 4b at Chang)

byteStringToIntegerExScript :: SerialisedScript
byteStringToIntegerExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () ByteStringToInteger @@ [ mkConstant @BS.ByteString () "hashme" ]

integerToByteStringExScript :: SerialisedScript
integerToByteStringExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () IntegerToByteString @@ [ mkConstant @Integer () 5, mkConstant @Integer () 123 ]

batch4bExScripts :: [(String, SerialisedScript)]
batch4bExScripts = [ ("byteStringToInteger", byteStringToIntegerExScript)
                   , ("integerToByteString", integerToByteStringExScript)
                   ]

-- Batch 5

-- First bitwise operation
andByteStringExScript :: SerialisedScript
andByteStringExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () AndByteString @@ [ mkConstant  () True
                              , mkConstant @BS.ByteString () "hashme"
                              , mkConstant @BS.ByteString () "andme" ]
-- Final bitwise operation
findFirstSetBitExScript :: SerialisedScript
findFirstSetBitExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () FindFirstSetBit @@ [ mkConstant @BS.ByteString () "hashme" ]


ripemd_160ExScript :: SerialisedScript
ripemd_160ExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () Ripemd_160 @@ [ mkConstant @BS.ByteString () "hashme" ]

batch5ExScripts :: [(String, SerialisedScript)]
batch5ExScripts = [ ("andByteString", andByteStringExScript)
                  , ("findFirstSetBit", findFirstSetBitExScript)
                  , ("ripemd_160", ripemd_160ExScript)]

-- Batch 6

expModIntegerExScript :: SerialisedScript
expModIntegerExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () ExpModInteger @@ [ mkConstant @Integer () 717812342342434234
                              , mkConstant @Integer () 897841231231231111
                              , mkConstant @Integer () 81931891
                              ]

dropListExScript :: SerialisedScript
dropListExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () DropList @@ [ mkConstant @Integer () 5
                         , mkConstant @[Text] () $
                           ["one", "two", "three", "four", "five", "six", "seven"]
                         ]

lengthOfArrayExScript :: SerialisedScript
lengthOfArrayExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () LengthOfArray @@ [ mkConstant @(Vector Text) () $
                                fromList ["one", "two", "three", "four", "five", "six", "seven"]
                              ]

listToArrayExScript :: SerialisedScript
listToArrayExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () ListToArray @@ [ mkConstant @[Text] ()
                              ["one", "two", "three", "four", "five", "six", "seven"]
                            ]

indexArrayExScript :: SerialisedScript
indexArrayExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
  builtin () IndexArray @@ [ mkConstant @Integer () 5
                           , mkConstant @(Vector Text) () $
                             fromList ["one", "two", "three", "four", "five", "six", "seven"]
                           ]

batch6ExScripts :: [(String, SerialisedScript)]
batch6ExScripts = [ ("expModInteger", expModIntegerExScript)
                  , ("dropList", dropListExScript)
                  , ("lengthOfArray", lengthOfArrayExScript)
                  , ("listToArray", listToArrayExScript)
                  , ("indexArrayE", indexArrayExScript)]

errorScript :: SerialisedScript
errorScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ UPLC.Error ()

v110script :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
v110script = UPLC.Program () PLC.plcVersion110 $ UPLC.Constr () 0 mempty

badConstrScript :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
badConstrScript = UPLC.Program () PLC.plcVersion100 $ UPLC.Constr () 0 mempty

badCaseScript :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
badCaseScript = UPLC.Program () PLC.plcVersion100 $ UPLC.Case () (UPLC.Error ()) mempty
