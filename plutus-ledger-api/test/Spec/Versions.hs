-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.Versions (tests) where

import PlutusCore as PLC
import PlutusCore.MkPlc as PLC
import PlutusCore.Version as PLC
import PlutusLedgerApi.Common
import PlutusLedgerApi.Common.Versions (batch1, batch2, batch3, batch4a, batch4b, batch5, batch6)
import PlutusPrelude
import UntypedPlutusCore as UPLC

import PlutusLedgerApi.Test.Scripts
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3

import Data.ByteString.Short qualified as BSS
import Data.Either
import Data.List ((\\))
import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

tests :: TestTree
tests = testGroup "versions"
    [ testLedgerLanguages
    , testLanguageVersions
    , testPermittedBuiltins
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

-- ** FIX THESE TOO
-- See Note [Checking the Plutus Core language version] for why these have to use mkTermToEvaluate
testLanguageVersions :: TestTree
testLanguageVersions = testGroup "Plutus Core language versions"
  [ testCase "v1.1.0 is available in PlutusV3/Chang and not before" $ do
      -- `LedgerLanguageNotAvailableError` is checked in `deserialiseScript`
      assertBool "in PlutusV3/,Vasil" $
        isLeft $ uplcToScriptForEvaluation PlutusV3 vasilPV v110script
      -- `PlutusCoreLanguageNotAvailableError` is checked in `mkTermToEvaluate`
      assertBool "in PlutusV2/Chang" $ isLeft $
        mkTermToEvaluate PlutusV2 changPV
        (either (Prelude.error . show)
          id
         (V2.deserialiseScript changPV $ serialiseUPLC v110script)
        ) []
      -- Both `deserialiseScript` and `mkTermToEvaluate` should succeed
      assertBool "not in PlutusV3/Chang" $ isRight $ mkTermToEvaluate PlutusV3 changPV
        (either (Prelude.error . show)
         id
         (V3.deserialiseScript changPV $ serialiseUPLC v110script)
        ) []
    -- The availability of `case` and `constr` is checked in `deserialise`
  , testCase "constr is not available with v1.0.0 ever" $
    assertBool "in PlutusV3/future" $
    isLeft $ uplcToScriptForEvaluation PlutusV3 changPV badConstrScript
  , testCase "case is not available with v1.0.0 ever" $
    assertBool "in PlutusV3/future" $
    isLeft $ uplcToScriptForEvaluation PlutusV3 changPV badCaseScript
  ]

-- * UPLC examples to test deserialisation

errorScript :: SerialisedScript
errorScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ UPLC.Error ()

v110script :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
v110script = UPLC.Program () PLC.plcVersion110 $ UPLC.Constr () 0 mempty

badConstrScript :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
badConstrScript = UPLC.Program () PLC.plcVersion100 $ UPLC.Constr () 0 mempty

badCaseScript :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
badCaseScript = UPLC.Program () PLC.plcVersion100 $ UPLC.Case () (UPLC.Error ()) mempty

-- Testing deserialisation checks for builtins

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
testPermittedBuiltins :: TestTree
testPermittedBuiltins =
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

-- Test that the checks for extra bytes after ends of scripts behave properly
deriving newtype instance Arbitrary MajorProtocolVersion

testRmdr :: TestTree
testRmdr = testGroup "extra bytes after end of script"
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

