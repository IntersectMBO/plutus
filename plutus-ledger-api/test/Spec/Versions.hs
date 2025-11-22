-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.Versions (tests) where

import PlutusCore as PLC
import PlutusCore.MkPlc as PLC
import PlutusCore.Version as PLC
import PlutusLedgerApi.Common
import PlutusPrelude
import UntypedPlutusCore as UPLC

import PlutusLedgerApi.Common.Versions

import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3

import Data.ByteString.Short qualified as BSS
import Data.Either
import Data.List ((\\))
import Data.Map qualified as Map
import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

tests :: TestTree
tests =
  testGroup
    "versions"
    [ testLedgerLanguages
    , testLanguageVersions
    , testPermittedBuiltins
    , testBuiltinAvailabilityCompatibility
    , testRmdr
    ]

allPVs :: [MajorProtocolVersion]
allPVs = [shelleyPV .. newestPV]

showPV :: MajorProtocolVersion -> String
showPV (MajorProtocolVersion pv) =
  case pv of
    2 -> "Shelley (PV2)"
    3 -> "Allegra (PV3)"
    4 -> "Mary (PV4)"
    5 -> "Alonzo (PV5)"
    6 -> "(Lobster) (PV6)"
    7 -> "Vasil (PV7)"
    8 -> "Valentine (PV8)"
    9 -> "Chang (PV9)"
    10 -> "Plomin (PV10)"
    11 -> "PV11"
    _ -> "<unknown> (PV" ++ show pv ++ ")"

-- Some scripts for use in the version tests.
errorScript :: SerialisedScript
errorScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ UPLC.Error ()

v100script :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
v100script = UPLC.Program () PLC.plcVersion100 $ UPLC.Constant () (PLC.Some (PLC.ValueOf PLC.DefaultUniUnit ()))

v110script :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
v110script = UPLC.Program () PLC.plcVersion110 $ UPLC.Constr () 0 mempty

badConstrScript :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
badConstrScript = UPLC.Program () PLC.plcVersion100 $ UPLC.Constr () 0 mempty

badCaseScript :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
badCaseScript = UPLC.Program () PLC.plcVersion100 $ UPLC.Case () (UPLC.Error ()) mempty

{- Given a UPLC term, serialise it then deserialise it for use in a particular
   LL/PV combination, checking whether or not it deserialises successfully.  See
   Note [Checking the Plutus Core language version] for why this has to use
   `mkTermToEvaluate`. Both `deserialiseScript` and `mkTermToEvaluate` can
   produce script decoding errors (for different reasons) and we intercept these
   and return them as `Left` values.  Any other errors will cause `error` to be
   invoked.
-}
mkTestTerm
  :: PlutusLedgerLanguage
  -> MajorProtocolVersion
  -> UPLC.Program DeBruijn DefaultUni DefaultFun ()
  -> Either ScriptDecodeError (UPLC.Term NamedDeBruijn DefaultUni DefaultFun ())
mkTestTerm ll pv prog =
  case deserialiseScript ll pv $ serialiseUPLC prog of
    Right s ->
      case mkTermToEvaluate ll pv s [] of
        Right t -> Right t
        Left (CodecError e) -> Left e
        Left e -> Prelude.error $ show e
    Left e -> Left e

-- Test that the different Plutus Core ledger languages are available in the
-- expected protocol versions and not in others.
testLedgerLanguages :: TestTree
testLedgerLanguages =
  testGroup
    "ledger languages"
    [ testProperty "PlutusV1 not before but after" $ prop_notBeforeButAfter V1.deserialiseScript alonzoPV
    , testProperty "PlutusV2 not before but after" $ prop_notBeforeButAfter V2.deserialiseScript vasilPV
    , testProperty "PlutusV3 not before but after" $ prop_notBeforeButAfter V3.deserialiseScript changPV
    , testProperty "protocol-versions can add but not remove ledger languages" $
        \pvA pvB -> pvA < pvB ==> ledgerLanguagesAvailableIn pvA `Set.isSubsetOf` ledgerLanguagesAvailableIn pvB
    ]
  where
    prop_notBeforeButAfter
      :: (MajorProtocolVersion -> SerialisedScript -> Either ScriptDecodeError b)
      -> MajorProtocolVersion
      -> MajorProtocolVersion
      -> Bool
    prop_notBeforeButAfter phase1Func expectedPv genPv =
      -- run phase 1 on an example script
      let resPhase1 = phase1Func genPv errorScript
       in if genPv < expectedPv
            -- generated an old protocol version
            then case resPhase1 of
              Left LedgerLanguageNotAvailableError {} -> True
              _ -> False
            -- generated an eq or gt the expected protocol version
            else isRight resPhase1

-- Test that the different Plutus Core language versions are available in the
-- expected LL/PV combinations.
testLanguageVersions :: TestTree
testLanguageVersions =
  testGroup "Plutus Core language versions" $
    let expectGood plcv prog ll pv =
          testCase ("Ok in " ++ showPV pv) $
            assertBool (plcv ++ " not allowed in " ++ show ll ++ " @" ++ showPV pv) $
              isRight $
                mkTestTerm ll pv prog
        expectBad plcv prog ll pv =
          testCase ("Not in " ++ showPV pv) $
            assertBool (plcv ++ " should not be allowed in " ++ show ll ++ " @" ++ showPV pv) $
              isLeft $
                mkTestTerm ll pv prog
        testOkFrom plcv ll firstGood prog =
          let expectedGood = [firstGood .. newestPV]
           in testGroup (show ll) $
                fmap (expectBad plcv prog ll) (allPVs \\ expectedGood)
                  ++ fmap (expectGood plcv prog ll) expectedGood
     in [ testGroup
            "v1.0.0 availability"
            [ testOkFrom "v100" PlutusV1 alonzoPV v100script
            , testOkFrom "v100" PlutusV2 vasilPV v100script
            , testOkFrom "v100" PlutusV3 changPV v100script
            ]
        , testGroup
            "v1.1.0 availability"
            [ testOkFrom "v110" PlutusV1 newestPV v110script
            , testOkFrom "v110" PlutusV2 newestPV v110script
            , testOkFrom "v110" PlutusV3 changPV v110script
            ]
        , -- Check that case and constr are not allowed in 1.1.0 in any LL/PV combination
          testCase "case is not available in v1.0.0 ever" $
            sequence_
              [ assertBool ("case unexpectedly allowed in " ++ show ll ++ " @PV" ++ show pv) $
                  isLeft $
                    mkTestTerm ll pv badCaseScript
              | ll <- enumerate
              , pv <- allPVs
              ]
        , testCase "constr is not available in v1.0.0 ever" $
            sequence_
              [ assertBool ("constr unexpectedly allowed in " ++ show ll ++ " @PV" ++ show pv) $
                  isLeft $
                    mkTestTerm ll pv badConstrScript
              | ll <- enumerate
              , pv <- allPVs
              ]
        ]

-- Testing deserialisation checks for builtins

{-| Make small scripts containing each builtin and check that the expected
   builtins are successfully deserialised in each PV/LL combination (and
   unexpected builtins cause an error during deserialisation.  These MUST BE
   EXTENDED when new builtins are deployed. -}

-- Should we test plcVersion110 as well?
mkScriptForBuiltin :: DefaultFun -> (String, SerialisedScript)
mkScriptForBuiltin fun =
  (show fun, serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ builtin () fun)

mkScriptsForBuiltins :: [DefaultFun] -> [(String, SerialisedScript)]
mkScriptsForBuiltins = fmap mkScriptForBuiltin

builtins1 :: [(String, SerialisedScript)]
builtins1 = mkScriptsForBuiltins batch1

builtins2 :: [(String, SerialisedScript)]
builtins2 = mkScriptsForBuiltins batch2

builtins3 :: [(String, SerialisedScript)]
builtins3 = mkScriptsForBuiltins batch3

builtins4a :: [(String, SerialisedScript)]
builtins4a = mkScriptsForBuiltins batch4a

builtins4b :: [(String, SerialisedScript)]
builtins4b = mkScriptsForBuiltins batch4b

builtins5 :: [(String, SerialisedScript)]
builtins5 = mkScriptsForBuiltins batch5

builtins6 :: [(String, SerialisedScript)]
builtins6 = mkScriptsForBuiltins batch6

allBuiltins :: [(String, SerialisedScript)]
allBuiltins =
  builtins1
    ++ builtins2
    ++ builtins3
    ++ builtins4a
    ++ builtins4b
    ++ builtins5
    ++ builtins6

{-| Test that the builtins that we expect to be allowed in each LL/PV
  combination can be successfully deserialised and that the rest cannot.  This
  is mostly testing that `builtinsAvailableIn` does what it's supposed to.
  This should be updated when new builtins, ledger languages, or protocol
  versions are added, but we expect that after Anon all builtins will be
  allowed in all ledger languages. -}

{- FIXME: Ideally we'd test that for PV11 scripts, all of the newer builtins
   have the same cost in each Plutus ledger language.  That would involve having
   appropriate sets of cost model parameters to feed into the parameter update
   process though.
-}
testPermittedBuiltins :: TestTree
testPermittedBuiltins =
  let testBuiltins ll deserialise pv expectedGood =
        let expectGood scripts =
              for_ scripts $ \(name, script) ->
                assertBool (name ++ " should be allowed in " ++ show ll ++ " @" ++ showPV pv) $
                  isRight $
                    deserialise pv script
            expectBad scripts =
              for_ scripts $ \(name, script) ->
                assertBool (name ++ " should not be allowed in " ++ show ll ++ " @" ++ showPV pv) $
                  isLeft $
                    deserialise pv script
         in testCase (showPV pv) $ do
              expectGood expectedGood
              expectBad (allBuiltins \\ expectedGood)
   in testGroup
        "Builtins allowed"
        [ let mkTest = testBuiltins PlutusV1 V1.deserialiseScript
           in testGroup
                "PlutusV1"
                [ mkTest shelleyPV []
                , mkTest allegraPV []
                , mkTest maryPV []
                , mkTest alonzoPV builtins1
                , mkTest vasilPV builtins1
                , mkTest valentinePV builtins1
                , mkTest changPV builtins1
                , mkTest plominPV builtins1
                , mkTest newestPV allBuiltins
                ]
        , let mkTest = testBuiltins PlutusV2 V2.deserialiseScript
           in testGroup
                "PlutusV2"
                [ mkTest shelleyPV []
                , mkTest allegraPV []
                , mkTest maryPV []
                , mkTest alonzoPV []
                , mkTest vasilPV $ builtins1 ++ builtins2
                , mkTest valentinePV $ builtins1 ++ builtins2 ++ builtins3
                , mkTest changPV $ builtins1 ++ builtins2 ++ builtins3
                , mkTest plominPV $ builtins1 ++ builtins2 ++ builtins3 ++ builtins4b
                , mkTest newestPV allBuiltins
                ]
        , let mkTest = testBuiltins PlutusV3 V3.deserialiseScript
           in testGroup
                "PlutusV3"
                [ mkTest shelleyPV []
                , mkTest allegraPV []
                , mkTest maryPV []
                , mkTest alonzoPV []
                , mkTest vasilPV []
                , mkTest valentinePV []
                , mkTest changPV $ builtins1 ++ builtins2 ++ builtins3 ++ builtins4a ++ builtins4b
                , mkTest plominPV $ builtins1 ++ builtins2 ++ builtins3 ++ builtins4a ++ builtins4b ++ builtins5
                , mkTest newestPV allBuiltins
                ]
        ]

{- It's important that the results returned by `builtinsAvailableIn` don't change.
   The implementation changed when we enabled all builtins in all ledger
   languages in PV11, so this test compares the results returned by the old and
   new versions to make sure that they're the same up to PV10 (the old version's
   been transplanted from PlutusLedgerApi.Common.Versions into the test below).
   A little care is required because the old version can return a nonempty
   result for an (LL,PV) combination where LL didn't actually exist in PV but
   the new version returns the empty set in this case: to avoid this we only
   test pairs where LL was available in PV.
-}
{- DON'T CHANGE THIS: it tests only up to PV10 and should never need to be extended. -}
testBuiltinAvailabilityCompatibility :: TestTree
testBuiltinAvailabilityCompatibility =
  testCase "Old and new versions of builtinsAvailableIn are compatible" $
    let builtinsIntroducedIn_old
          :: Map.Map (PlutusLedgerLanguage, MajorProtocolVersion) (Set.Set DefaultFun)
        builtinsIntroducedIn_old =
          Map.fromList
            [
              ( (PlutusV1, alonzoPV)
              , Set.fromList
                  [ AddInteger
                  , SubtractInteger
                  , MultiplyInteger
                  , DivideInteger
                  , QuotientInteger
                  , RemainderInteger
                  , ModInteger
                  , EqualsInteger
                  , LessThanInteger
                  , LessThanEqualsInteger
                  , AppendByteString
                  , ConsByteString
                  , SliceByteString
                  , LengthOfByteString
                  , IndexByteString
                  , EqualsByteString
                  , LessThanByteString
                  , LessThanEqualsByteString
                  , Sha2_256
                  , Sha3_256
                  , Blake2b_256
                  , VerifyEd25519Signature
                  , AppendString
                  , EqualsString
                  , EncodeUtf8
                  , DecodeUtf8
                  , IfThenElse
                  , ChooseUnit
                  , Trace
                  , FstPair
                  , SndPair
                  , ChooseList
                  , MkCons
                  , HeadList
                  , TailList
                  , NullList
                  , ChooseData
                  , ConstrData
                  , MapData
                  , ListData
                  , IData
                  , BData
                  , UnConstrData
                  , UnMapData
                  , UnListData
                  , UnIData
                  , UnBData
                  , EqualsData
                  , MkPairData
                  , MkNilData
                  , MkNilPairData
                  ]
              )
            ,
              ( (PlutusV2, vasilPV)
              , Set.fromList
                  [SerialiseData]
              )
            ,
              ( (PlutusV2, valentinePV)
              , Set.fromList
                  [VerifyEcdsaSecp256k1Signature, VerifySchnorrSecp256k1Signature]
              )
            ,
              ( (PlutusV2, plominPV)
              , Set.fromList
                  [IntegerToByteString, ByteStringToInteger]
              )
            ,
              ( (PlutusV3, changPV)
              , Set.fromList
                  [ Bls12_381_G1_add
                  , Bls12_381_G1_neg
                  , Bls12_381_G1_scalarMul
                  , Bls12_381_G1_equal
                  , Bls12_381_G1_hashToGroup
                  , Bls12_381_G1_compress
                  , Bls12_381_G1_uncompress
                  , Bls12_381_G2_add
                  , Bls12_381_G2_neg
                  , Bls12_381_G2_scalarMul
                  , Bls12_381_G2_equal
                  , Bls12_381_G2_hashToGroup
                  , Bls12_381_G2_compress
                  , Bls12_381_G2_uncompress
                  , Bls12_381_millerLoop
                  , Bls12_381_mulMlResult
                  , Bls12_381_finalVerify
                  , Keccak_256
                  , Blake2b_224
                  , IntegerToByteString
                  , ByteStringToInteger
                  ]
              )
            ,
              ( (PlutusV3, plominPV)
              , Set.fromList
                  [ AndByteString
                  , OrByteString
                  , XorByteString
                  , ComplementByteString
                  , ReadBit
                  , WriteBits
                  , ReplicateByte
                  , ShiftByteString
                  , RotateByteString
                  , CountSetBits
                  , FindFirstSetBit
                  , Ripemd_160
                  ]
              )
            ]
        builtinsAvailableIn_old
          :: PlutusLedgerLanguage
          -> MajorProtocolVersion
          -> Set.Set DefaultFun
        builtinsAvailableIn_old thisLv thisPv =
          fold $
            Map.filterWithKey (const . alreadyIntroduced) builtinsIntroducedIn_old
          where
            alreadyIntroduced :: (PlutusLedgerLanguage, MajorProtocolVersion) -> Bool
            alreadyIntroduced (introducedInLv, introducedInPv) =
              -- both should be satisfied
              introducedInLv <= thisLv && introducedInPv <= thisPv
     in sequence_
          [ assertBool
              ( "Old and new versions of builtinsAvailableIn differ for "
                  ++ show ll
                  ++ " @PV"
                  ++ show pv
              )
              $ builtinsAvailableIn ll pv == builtinsAvailableIn_old ll pv
          | pv <- [shelleyPV .. plominPV]
          , ll <- Set.toList (ledgerLanguagesAvailableIn pv)
          ]

-- Test that the checks for extra bytes after ends of scripts behave properly.
deriving newtype instance Arbitrary MajorProtocolVersion

testRmdr :: TestTree
testRmdr =
  testGroup
    "extra bytes after end of script"
    [ testCase "remdr" $ do
        assertBool "remdr1" $ isRight $ V1.deserialiseScript valentinePV $ errorScript <> "remdr1"
        assertBool "remdr2" $ isRight $ V2.deserialiseScript valentinePV $ errorScript <> "remdr2"
        assertBool "remdr1c" $ isRight $ V1.deserialiseScript changPV $ errorScript <> "remdr1"
        assertBool "remdr2c" $ isRight $ V2.deserialiseScript changPV $ errorScript <> "remdr2"
        assertEqual "remdr3" (RemainderError "remdr3") $ fromLeft (Prelude.error "Expected Reft, got Right") $ V3.deserialiseScript changPV $ errorScript <> "remdr3"
    , testProperty "remdr1gen" $ \remdr -> isRight $ V1.deserialiseScript valentinePV $ errorScript <> BSS.pack remdr
    , testProperty "remdr2gen" $ \remdr -> isRight $ V2.deserialiseScript valentinePV $ errorScript <> BSS.pack remdr
    , testProperty "remdr1genc" $ \remdr -> isRight $ V1.deserialiseScript changPV $ errorScript <> BSS.pack remdr
    , testProperty "remdr2genc" $ \remdr -> isRight $ V2.deserialiseScript changPV $ errorScript <> BSS.pack remdr
    -- we cannot make the same property as above for remdr3gen because it may generate valid bytestring append extensions to the original script
    -- a more sophisticated one could work though
    ]
