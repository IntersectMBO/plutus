{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Evaluation.Patterns (test_patterns) where

import Data.ByteString qualified as BS
import Data.Functor.Identity (runIdentity)
import Data.Int (Int64)
import Data.List (foldl')
import Data.Vector qualified as Vector
import Data.Word (Word64)
import PlutusCore.Data qualified as PLC
import PlutusCore.Default
  ( DefaultBuiltinPattern (..)
  , DefaultFun (..)
  , DefaultUni
  )
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..), ExRestrictingBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Evaluation.Machine.Exception
  ( MachineError (NonFunctionalApplicationMachineError)
  )
import PlutusCore.Evaluation.Machine.MachineParameters
  ( MachineParameters (..)
  , MachineVariantParameters (..)
  )
import PlutusCore.MkPlc (mkConstant, mkIterAppNoAnn)
import PlutusCore.Name.Unique (Name (..), Unique (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
  ( cekMatchCost
  , cekPatternCost
  , cekPatternFailureCost
  , cekPatternStructuralCost
  , unitCekMachineCosts
  )
import UntypedPlutusCore.Evaluation.Machine.SteppableCek qualified as SteppableCek

type UTerm = UPLC.Term Name DefaultUni DefaultFun DefaultBuiltinPattern ()

patternChildren
  :: (Vector.Vector DefaultBuiltinPattern -> DefaultBuiltinPattern)
  -> [DefaultBuiltinPattern]
  -> DefaultBuiltinPattern
patternChildren constructor = constructor . Vector.fromList

dataConstrPattern
  :: Word64
  -> [DefaultBuiltinPattern]
  -> DefaultBuiltinPattern
dataConstrPattern tag = patternChildren (DefaultPatternDataConstr tag)

dataIPattern :: DefaultBuiltinPattern -> DefaultBuiltinPattern
dataIPattern = DefaultPatternDataI . Just

dataBPattern :: DefaultBuiltinPattern -> DefaultBuiltinPattern
dataBPattern = DefaultPatternDataB . Just

pairPattern :: DefaultBuiltinPattern -> DefaultBuiltinPattern -> DefaultBuiltinPattern
pairPattern = DefaultPatternPair

matchSingle :: DefaultBuiltinPattern -> UTerm -> UTerm -> UTerm
matchSingle pat handler scrutinee =
  UPLC.Match () scrutinee $ Vector.singleton (pat, handler)

constantData :: PLC.Data -> UTerm
constantData = mkConstant @PLC.Data ()

constantInteger :: Integer -> UTerm
constantInteger = mkConstant @Integer ()

assertBothEvaluateTo :: UTerm -> UTerm -> IO ()
assertBothEvaluateTo expected term = do
  Cek.evaluateCekNoEmit defaultCekParametersForTesting term @?= Right expected
  SteppableCek.evaluateCekNoEmit defaultCekParametersForTesting term @?= Right expected

assertBothFail :: UTerm -> IO ()
assertBothFail term = do
  assertFails "CEK" $ Cek.evaluateCekNoEmit defaultCekParametersForTesting term
  assertFails "steppable CEK" $ SteppableCek.evaluateCekNoEmit defaultCekParametersForTesting term
  where
    assertFails machine = \case
      Left _ -> pure ()
      Right result -> assertFailure $ machine <> " unexpectedly returned " <> show result

assertBothFailNonFunctionalWithoutCause :: UTerm -> IO ()
assertBothFailNonFunctionalWithoutCause term = do
  assertExpectedFailure "CEK" $ Cek.evaluateCekNoEmit defaultCekParametersForTesting term
  assertExpectedFailure "steppable CEK" $
    SteppableCek.evaluateCekNoEmit defaultCekParametersForTesting term
  where
    assertExpectedFailure machine = \case
      Left
        ( Cek.ErrorWithCause
            (Cek.StructuralError NonFunctionalApplicationMachineError)
            Nothing
          ) -> pure ()
      result ->
        assertFailure $
          machine <> " did not fail with a cause-free non-functional application: " <> show result

assertBothRunOutOfBudget :: UTerm -> IO ()
assertBothRunOutOfBudget term = do
  assertOutOfBudget "CEK" . fst $
    Cek.runCekNoEmit defaultCekParametersForTesting (Cek.restricting nearMaximumCpuBudget) term
  assertOutOfBudget "steppable CEK" . fst $
    SteppableCek.runCekNoEmit
      defaultCekParametersForTesting
      (Cek.restricting nearMaximumCpuBudget)
      term
  where
    -- Keep incremental-exhaustion tests fast enough for the regular test suite.
    nearMaximumCpuBudget = ExRestrictingBudget $ ExBudget 40000000 1000000000
    assertOutOfBudget machine = \case
      Left (Cek.ErrorWithCause (Cek.OperationalError (Cek.CekOutOfExError _)) _) -> pure ()
      result -> assertFailure $ machine <> " did not stop with an out-of-budget error: " <> show result

defaultParameters
  :: MachineParameters
       Cek.CekMachineCosts
       DefaultFun
       (Cek.CekValue DefaultUni DefaultFun DefaultBuiltinPattern ())
       DefaultBuiltinPattern
defaultParameters = defaultCekParametersForTesting

unitParameters
  :: MachineParameters
       Cek.CekMachineCosts
       DefaultFun
       (Cek.CekValue DefaultUni DefaultFun DefaultBuiltinPattern ())
       DefaultBuiltinPattern
unitParameters = case defaultParameters of
  MachineParameters caser matcher (MachineVariantParameters _ runtime) ->
    MachineParameters caser matcher (MachineVariantParameters unitCekMachineCosts runtime)

selectedStepOnly
  :: Cek.StepKind
  -> Cek.ExBudgetMode ExBudget DefaultUni DefaultFun DefaultBuiltinPattern
selectedStepOnly wanted = Cek.monoidalBudgeting $ \category budget -> case category of
  Cek.BStep actual | actual == wanted -> budget
  _ -> mempty

selectedPatternOnly
  :: Cek.ExBudgetMode ExBudget DefaultUni DefaultFun DefaultBuiltinPattern
selectedPatternOnly = Cek.monoidalBudgeting $ \category budget -> case category of
  Cek.BPattern -> budget
  _ -> mempty

stepBudget :: Cek.StepKind -> UTerm -> ExBudget
stepBudget wanted term =
  snd $ Cek.runCekNoEmit unitParameters (selectedStepOnly wanted) term

steppableStepBudget :: Cek.StepKind -> UTerm -> ExBudget
steppableStepBudget wanted term =
  snd $ SteppableCek.runCekNoEmit unitParameters (selectedStepOnly wanted) term

patternBudget :: UTerm -> ExBudget
patternBudget term = snd $ Cek.runCekNoEmit unitParameters selectedPatternOnly term

steppablePatternBudget :: UTerm -> ExBudget
steppablePatternBudget term = snd $ SteppableCek.runCekNoEmit unitParameters selectedPatternOnly term

captureHandler :: UTerm
captureHandler =
  UPLC.LamAbs () x $
    UPLC.LamAbs () y $
      UPLC.LamAbs () z $
        UPLC.Var () y
  where
    x = Name "x" (Unique 0)
    y = Name "y" (Unique 1)
    z = Name "z" (Unique 2)

capturePattern :: DefaultBuiltinPattern
capturePattern =
  dataConstrPattern
    1
    [DefaultPatternCapture, DefaultPatternCapture, DefaultPatternCapture]

captureScrutinee :: UTerm
captureScrutinee = constantData $ PLC.Constr 1 [PLC.I 1, PLC.I 2, PLC.I 3]

captureTerm :: UTerm
captureTerm = matchSingle capturePattern captureHandler captureScrutinee

totalBudget :: UTerm -> ExBudget
totalBudget term = case Cek.runCekNoEmit defaultParameters Cek.counting term of
  (_, Cek.CountingSt budget) -> budget

{-| Match a particular @Data.Constr@ tag and exact field count using only the traditional builtins.
All non-constructor, wrong-tag, and wrong-arity inputs take the fallback, just as they do in the
corresponding ordered 'UPLC.Match'. -}
traditionalDataConstrMatch :: Int -> UTerm
traditionalDataConstrMatch = snd . traditionalDataConstrMatches

traditionalUnConstrDataMatch :: Int -> UTerm
traditionalUnConstrDataMatch = fst . traditionalDataConstrMatches

traditionalDataConstrMatches :: Int -> (UTerm, UTerm)
traditionalDataConstrMatches width =
  ( constrBranch
  , UPLC.Force () $
      mkIterAppNoAnn
        (UPLC.Force () $ UPLC.Builtin () ChooseData)
        [ scrutinee
        , UPLC.Delay () constrBranch
        , UPLC.Delay () fallback
        , UPLC.Delay () fallback
        , UPLC.Delay () fallback
        , UPLC.Delay () fallback
        ]
  )
  where
    scrutinee = constantData . PLC.Constr 42 $ replicate width (PLC.I 0)
    success = constantInteger 1
    fallback = constantInteger 0
    tagName = Name "tag" (Unique 1000)
    fieldsName = Name "fields" (Unique 1001)
    fieldName index = Name "field" . Unique $ 2000 + 2 * index
    restName index = Name "rest" . Unique $ 2001 + 2 * index
    exactFields index fields
      | index == width =
          UPLC.Case
            ()
            fields
            ( Vector.fromList
                [ UPLC.LamAbs () (fieldName index) $
                    UPLC.LamAbs () (restName index) fallback
                , success
                ]
            )
      | otherwise =
          UPLC.Case
            ()
            fields
            ( Vector.fromList
                [ UPLC.LamAbs () (fieldName index) $
                    UPLC.LamAbs () (restName index) $
                      exactFields (index + 1) (UPLC.Var () $ restName index)
                , fallback
                ]
            )
    tagMatches =
      mkIterAppNoAnn
        (UPLC.Builtin () EqualsInteger)
        [UPLC.Var () tagName, constantInteger 42]
    constrBranch =
      UPLC.Case
        ()
        (mkIterAppNoAnn (UPLC.Builtin () UnConstrData) [scrutinee])
        ( Vector.singleton $
            UPLC.LamAbs () tagName $
              UPLC.LamAbs () fieldsName $
                UPLC.Case
                  ()
                  tagMatches
                  ( Vector.fromList
                      [ fallback
                      , exactFields 0 (UPLC.Var () fieldsName)
                      ]
                  )
        )

matchDataConstrWildcards :: Int -> UTerm
matchDataConstrWildcards width =
  UPLC.Match
    ()
    scrutinee
    ( Vector.fromList
        [ (dataConstrPattern 42 $ replicate width DefaultPatternWildcard, constantInteger 1)
        , (DefaultPatternWildcard, constantInteger 0)
        ]
    )
  where
    scrutinee = constantData . PLC.Constr 42 $ replicate width (PLC.I 0)

matchDataConstrCaptures :: Int -> UTerm
matchDataConstrCaptures width =
  UPLC.Match
    ()
    scrutinee
    ( Vector.fromList
        [ (dataConstrPattern 42 $ replicate width DefaultPatternCapture, handler)
        , (DefaultPatternWildcard, constantInteger 0)
        ]
    )
  where
    scrutinee = constantData . PLC.Constr 42 $ replicate width (PLC.I 0)
    captureName index = Name "capture" . Unique $ 3000 + index
    handler = foldr (UPLC.LamAbs () . captureName) (constantInteger 1) [0 .. width - 1]

nestedDataPattern :: DefaultBuiltinPattern
nestedDataPattern =
  patternChildren
    DefaultPatternDataList
    [ dataConstrPattern
        0
        [dataIPattern $ DefaultPatternInteger 1]
    ]

nestedCapturePattern :: DefaultBuiltinPattern
nestedCapturePattern =
  dataConstrPattern
    9
    [ patternChildren
        DefaultPatternDataList
        [ dataIPattern DefaultPatternCapture
        , DefaultPatternCapture
        ]
    , dataBPattern DefaultPatternCapture
    ]

nestedCaptureScrutinee :: UTerm
nestedCaptureScrutinee =
  constantData $ PLC.Constr 9 [PLC.List [PLC.I 11, PLC.I 22], PLC.B "abc"]

selectCaptureHandler :: Int -> UTerm
selectCaptureHandler selected =
  UPLC.LamAbs () first $
    UPLC.LamAbs () second $
      UPLC.LamAbs () third $
        UPLC.Var () $
          [first, second, third] !! selected
  where
    first = Name "first" (Unique 10)
    second = Name "second" (Unique 11)
    third = Name "third" (Unique 12)

test_patterns :: TestTree
test_patterns =
  testGroup
    "patterns"
    [ testCase "single-alternative Data Constr tag/arity match captures fields left-to-right" $
        assertBothEvaluateTo (constantData $ PLC.I 2) captureTerm
    , testCase "Match is built-in-only and does not match a UPLC Constr" $
        assertBothFail $
          matchSingle DefaultPatternWildcard (constantInteger 1) (UPLC.Constr () 0 [])
    , testCase "ordered Match matches an arbitrary integer value" $ do
        let term =
              UPLC.Match
                ()
                (constantInteger 42)
                ( Vector.fromList
                    [ (DefaultPatternInteger 7, constantInteger 70)
                    , (DefaultPatternInteger 42, constantInteger 420)
                    , (DefaultPatternWildcard, constantInteger 0)
                    ]
                )
        assertBothEvaluateTo (constantInteger 420) term
    , testCase "ordered Match matches a nested Data structure" $ do
        let scrutinee = constantData $ PLC.List [PLC.Constr 0 [PLC.I 1]]
            term =
              UPLC.Match
                ()
                scrutinee
                ( Vector.fromList
                    [ (dataConstrPattern 99 [], constantInteger 99)
                    , (nestedDataPattern, constantInteger 42)
                    , (DefaultPatternWildcard, constantInteger 0)
                    ]
                )
        assertBothEvaluateTo (constantInteger 42) term
    , testCase "ordered Match falls through to a wildcard" $ do
        let term =
              UPLC.Match
                ()
                (constantData $ PLC.B "not the nested value")
                ( Vector.fromList
                    [ (nestedDataPattern, constantInteger 42)
                    , (DefaultPatternWildcard, constantInteger 7)
                    ]
                )
        assertBothEvaluateTo (constantInteger 7) term
    , testCase "Data Map patterns expose entries as built-in pairs" $ do
        let entryPattern =
              pairPattern
                (dataIPattern $ DefaultPatternInteger 1)
                (dataBPattern $ DefaultPatternByteString "value")
            mapPattern = patternChildren DefaultPatternDataMap [entryPattern]
            term =
              UPLC.Match
                ()
                (constantData $ PLC.Map [(PLC.I 1, PLC.B "value")])
                ( Vector.fromList
                    [ (mapPattern, constantInteger 1)
                    , (DefaultPatternWildcard, constantInteger 0)
                    ]
                )
        assertBothEvaluateTo (constantInteger 1) term
    , testCase "built-in list patterns match an exact length" $ do
        let captured = Name "captured" (Unique 3)
            handler = UPLC.LamAbs () captured $ UPLC.Var () captured
            term =
              UPLC.Match
                ()
                (mkConstant @[Integer] () [1, 2, 3])
                ( Vector.fromList
                    [
                      ( patternChildren
                          DefaultPatternList
                          [DefaultPatternWildcard, DefaultPatternCapture, DefaultPatternWildcard]
                      , handler
                      )
                    , (DefaultPatternWildcard, constantInteger 0)
                    ]
                )
        assertBothEvaluateTo (constantInteger 2) term
    , testCase "nested captures are supplied depth-first and left-to-right" $ do
        let term selected =
              matchSingle nestedCapturePattern (selectCaptureHandler selected) nestedCaptureScrutinee
        assertBothEvaluateTo (constantInteger 11) $ term 0
        assertBothEvaluateTo (constantData $ PLC.I 22) $ term 1
        assertBothEvaluateTo (mkConstant @BS.ByteString () "abc") $ term 2
    , testCase "single-alternative Data Constr match rejects the wrong arity" $ do
        let wrongArity = constantData $ PLC.Constr 1 [PLC.I 1, PLC.I 2]
        assertBothFail $ matchSingle capturePattern captureHandler wrongArity
    , testCase "deep matching exhausts incrementally without stack overflow" $ do
        let depth :: Int
            depth = 100000
            deepPattern =
              foldl'
                (\pat _ -> patternChildren DefaultPatternDataList [pat])
                DefaultPatternWildcard
                [1 .. depth]
            deepData =
              foldl'
                (\value _ -> PLC.List [value])
                (PLC.I 0)
                [1 .. depth]
        -- Force the synthetic generators before entering either CEK. A Flat-decoded script already
        -- has these structures; charging arbitrary caller-supplied Haskell thunks is out of scope.
        deepPattern `seq`
          deepData `seq`
            assertBothRunOutOfBudget
              (matchSingle deepPattern (constantInteger 0) (constantData deepData))
    , testCase "wide all-wildcard matches do not require an uncharged flattening pass" $ do
        let width = 10000
            pat = patternChildren DefaultPatternList $ replicate width DefaultPatternWildcard
            term = matchSingle pat (constantInteger 1) $ mkConstant @[Integer] () (replicate width 0)
        assertBothEvaluateTo (constantInteger 1) term
    , testCase "a fixed-point loop repeatedly matching a wide pattern exhausts promptly" $ do
        let width = 2048
            self = Name "self" (Unique 4000)
            pat = patternChildren DefaultPatternList $ replicate width DefaultPatternWildcard
            scrutinee = mkConstant @[Integer] () $ replicate width 0
            loopBody =
              matchSingle
                pat
                (UPLC.Apply () (UPLC.Var () self) (UPLC.Var () self))
                scrutinee
            loop = UPLC.LamAbs () self loopBody
        assertBothRunOutOfBudget $ UPLC.Apply () loop loop
    , testCase "an early list child mismatch ignores the remaining values" $ do
        let width = 10000
            pat =
              patternChildren DefaultPatternList $
                DefaultPatternInteger 1 : replicate width (DefaultPatternInteger 0)
            term =
              UPLC.Match
                ()
                (mkConstant @[Integer] () $ replicate (width + 1) 0)
                ( Vector.fromList
                    [ (pat, constantInteger 0)
                    , (DefaultPatternWildcard, constantInteger 1)
                    ]
                )
        assertBothEvaluateTo (constantInteger 1) term
    , testCase "over-wide exact lists reject before visiting an unreachable child" $ do
        let depth :: Int
            depth = 10000
            deepPattern =
              foldl'
                (\pat _ -> patternChildren DefaultPatternDataList [pat])
                DefaultPatternWildcard
                [1 .. depth]
            deepData =
              foldl'
                (\value _ -> PLC.List [value])
                (PLC.I 0)
                [1 .. depth]
            term childPattern childValue =
              UPLC.Match
                ()
                (mkConstant @[PLC.Data] () [childValue, PLC.I 1])
                ( Vector.fromList
                    [ (patternChildren DefaultPatternList [childPattern], constantInteger 0)
                    , (DefaultPatternWildcard, constantInteger 1)
                    ]
                )
            shallowTerm = term DefaultPatternWildcard (PLC.I 0)
            deepTerm = term deepPattern deepData
            shallowBudget = ExBudget 4 0
        deepPattern `seq` deepData `seq` pure ()
        assertBothEvaluateTo (constantInteger 1) shallowTerm
        assertBothEvaluateTo (constantInteger 1) deepTerm
        patternBudget shallowTerm @?= shallowBudget
        steppablePatternBudget shallowTerm @?= shallowBudget
        patternBudget deepTerm @?= shallowBudget
        steppablePatternBudget deepTerm @?= shallowBudget
    , testCase "captured application rejects a deep non-functional handler without a cause" $ do
        let depth :: Int
            depth = 4096
            deepHandler =
              foldl'
                (\handler _ -> UPLC.Constr () 0 [handler])
                (UPLC.Constr () 0 [])
                [1 .. depth]
            term = matchSingle DefaultPatternCapture deepHandler (constantInteger 0)
        deepHandler `seq` assertBothFailNonFunctionalWithoutCause term
    , testCase "pattern work and synthetic capture applications are explicitly charged" $ do
        let exactConstr n child =
              matchSingle
                (dataConstrPattern 1 $ replicate n child)
                (constantInteger 0)
                (constantData . PLC.Constr 1 $ replicate n (PLC.I 0))
            noCaptureTerm = exactConstr 3 DefaultPatternWildcard
            matchNoCaptureTerm =
              UPLC.Match
                ()
                (constantData . PLC.Constr 1 $ replicate 3 (PLC.I 0))
                ( Vector.singleton
                    ( dataConstrPattern 1 $ replicate 3 DefaultPatternWildcard
                    , constantInteger 0
                    )
                )
        patternBudget (exactConstr 0 DefaultPatternWildcard) @?= ExBudget 2 0
        patternBudget noCaptureTerm @?= ExBudget 5 0
        patternBudget captureTerm @?= ExBudget 11 0
        patternBudget matchNoCaptureTerm @?= ExBudget 5 0
        stepBudget Cek.BApply noCaptureTerm @?= ExBudget 0 0
        stepBudget Cek.BApply captureTerm @?= ExBudget 0 0
    , testCase "every reached capture is charged before alternative selection completes" $ do
        let captured = Name "captured" (Unique 5000)
            first = Name "first" (Unique 5001)
            second = Name "second" (Unique 5002)
            identityHandler = UPLC.LamAbs () captured $ UPLC.Var () captured
            firstHandler =
              UPLC.LamAbs () first $ UPLC.LamAbs () second $ UPLC.Var () first
            secondHandler =
              UPLC.LamAbs () first $ UPLC.LamAbs () second $ UPLC.Var () second
            listMatch pats handler values =
              matchSingle
                (patternChildren DefaultPatternList pats)
                handler
                (mkConstant @[Integer] () values)
            rootCapture = matchSingle DefaultPatternCapture identityHandler (constantInteger 0)
            finalFieldCapture = listMatch [DefaultPatternCapture] identityHandler [0]
            nonFinalFieldCapture =
              listMatch
                [DefaultPatternCapture, DefaultPatternWildcard]
                identityHandler
                [0, 1]
            abandonedCaptures suffixWidth =
              UPLC.Match
                ()
                (mkConstant @[Integer] () $ replicate (3 + suffixWidth) 0)
                ( Vector.fromList
                    [
                      ( patternChildren DefaultPatternList $
                          [DefaultPatternCapture, DefaultPatternCapture, DefaultPatternInteger 1]
                            <> replicate suffixWidth DefaultPatternCapture
                      , firstHandler
                      )
                    , (DefaultPatternWildcard, constantInteger 1)
                    ]
                )
            abandonedCaptureWithSuffix suffixWidth =
              UPLC.Match
                ()
                (mkConstant @[Integer] () $ replicate (2 + suffixWidth) 0)
                ( Vector.fromList
                    [
                      ( patternChildren DefaultPatternList $
                          [DefaultPatternCapture, DefaultPatternInteger 1]
                            <> replicate suffixWidth DefaultPatternCapture
                      , identityHandler
                      )
                    , (DefaultPatternWildcard, constantInteger 1)
                    ]
                )
            resetCaptures =
              UPLC.Match
                ()
                (mkConstant @[Integer] () [10, 20])
                ( Vector.fromList
                    [
                      ( patternChildren
                          DefaultPatternList
                          [DefaultPatternCapture, DefaultPatternInteger 99]
                      , identityHandler
                      )
                    ,
                      ( patternChildren
                          DefaultPatternList
                          [DefaultPatternCapture, DefaultPatternCapture]
                      , secondHandler
                      )
                    ]
                )
            assertPatternBudget expected term = do
              patternBudget term @?= expected
              steppablePatternBudget term @?= expected
        assertBothEvaluateTo (constantInteger 0) rootCapture
        assertBothEvaluateTo (constantInteger 0) finalFieldCapture
        assertBothEvaluateTo (constantInteger 0) nonFinalFieldCapture
        assertBothEvaluateTo (constantInteger 1) $ abandonedCaptures 0
        assertBothEvaluateTo (constantInteger 1) $ abandonedCaptures 1000
        assertBothEvaluateTo (constantInteger 1) $ abandonedCaptureWithSuffix 0
        assertBothEvaluateTo (constantInteger 1) $ abandonedCaptureWithSuffix 1000
        assertBothEvaluateTo (constantInteger 20) resetCaptures
        assertPatternBudget (ExBudget 4 0) rootCapture
        assertPatternBudget (ExBudget 5 0) finalFieldCapture
        assertPatternBudget (ExBudget 6 0) nonFinalFieldCapture
        assertPatternBudget (ExBudget 10 0) $ abandonedCaptures 0
        assertPatternBudget (ExBudget 10 0) $ abandonedCaptures 1000
        assertPatternBudget (ExBudget 7 0) $ abandonedCaptureWithSuffix 0
        assertPatternBudget (ExBudget 7 0) $ abandonedCaptureWithSuffix 1000
    , testCase "the pre-activation Match coefficients cap ledger-scale work" $
        case defaultParameters of
          MachineParameters _ _ (MachineVariantParameters costs _) -> do
            runIdentity (cekMatchCost costs) @?= ExBudget 210000 100
            runIdentity (cekPatternCost costs) @?= ExBudget 2500 100
            runIdentity (cekPatternStructuralCost costs) @?= ExBudget 27500 60
            runIdentity (cekPatternFailureCost costs) @?= ExBudget 32500 100
    , testCase "Data.Constr Match costs less than direct and checked UnConstrData" $ do
        let assertCpuCheaper label candidateBudget baselineBudget =
              case (candidateBudget, baselineBudget) of
                (ExBudget candidateCpu _, ExBudget baselineCpu _) ->
                  assertBool
                    (label <> " CPU budget was not lower: " <> show (candidateBudget, baselineBudget))
                    (candidateCpu < baselineCpu)
            assertCheaper label candidate baseline =
              case (totalBudget candidate, totalBudget baseline) of
                ( candidateBudget@(ExBudget _ candidateMem)
                  , baselineBudget@(ExBudget _ baselineMem)
                  ) -> do
                    assertCpuCheaper label candidateBudget baselineBudget
                    assertBool
                      (label <> " memory budget was not lower: " <> show (candidateBudget, baselineBudget))
                      (candidateMem < baselineMem)
            expectedTraditional width =
              ExBudget
                (651396 + 64000 * fromIntegral width)
                (3165 + 400 * fromIntegral width)
            expectedDirectUnConstr width =
              ExBudget
                (317021 + 64000 * fromIntegral width)
                (1633 + 400 * fromIntegral width)
            expectedWildcards width =
              ExBudget
                (244600 + 27500 * fromIntegral width)
                (500 + 60 * fromIntegral width)
            expectedCaptures width =
              ExBudget
                (244600 + 48500 * fromIntegral width)
                (500 + 360 * fromIntegral width)
        mapM_
          ( \width -> do
              let traditional = traditionalDataConstrMatch width
                  directUnConstr = traditionalUnConstrDataMatch width
                  wildcards = matchDataConstrWildcards width
                  captures = matchDataConstrCaptures width
                  suffix = " at width " <> show width
              assertBothEvaluateTo (constantInteger 1) traditional
              assertBothEvaluateTo (constantInteger 1) directUnConstr
              assertBothEvaluateTo (constantInteger 1) wildcards
              assertBothEvaluateTo (constantInteger 1) captures
              totalBudget traditional @?= expectedTraditional width
              totalBudget directUnConstr @?= expectedDirectUnConstr width
              totalBudget wildcards @?= expectedWildcards width
              totalBudget captures @?= expectedCaptures width
              assertCheaper ("wildcard Match" <> suffix) wildcards traditional
              assertCheaper ("capture Match" <> suffix) captures traditional
              assertCheaper ("wildcard Match versus direct UnConstrData" <> suffix) wildcards directUnConstr
              assertCheaper
                ("capture Match versus direct UnConstrData" <> suffix)
                captures
                directUnConstr
          )
          [0, 1, 3, 16]
    , testCase "fixed-width integer and Data tag patterns have constant scalar cost" $ do
        let integerTerm expected =
              matchSingle
                (DefaultPatternInteger expected)
                (constantInteger 0)
                (constantInteger $ toInteger expected)
            smallBytes = "a"
            largeBytes = BS.replicate 65 97
            bytesTerm bytes =
              matchSingle
                (DefaultPatternByteString bytes)
                (constantInteger 0)
                (mkConstant @BS.ByteString () bytes)
            dataConstrTerm tag =
              matchSingle
                (dataConstrPattern tag [])
                (constantInteger 0)
                (constantData $ PLC.Constr (toInteger tag) [])
            integerTerms =
              [ integerTerm (minBound :: Int64)
              , integerTerm 0
              , integerTerm (maxBound :: Int64)
              ]
            dataConstrTerms =
              [dataConstrTerm 0, dataConstrTerm (maxBound :: Word64)]
        mapM_ (\term -> patternBudget term @?= ExBudget 2 0) integerTerms
        mapM_ (\term -> patternBudget term @?= ExBudget 2 0) dataConstrTerms
        patternBudget (bytesTerm smallBytes) @?= ExBudget 3 0
        patternBudget (bytesTerm largeBytes) @?= ExBudget 11 0
        mapM_
          ( \term -> do
              assertBothEvaluateTo (constantInteger 0) term
              steppablePatternBudget term @?= patternBudget term
          )
          (integerTerms <> dataConstrTerms)
    , testCase "exact-list matching charges only the traversed prefix" $ do
        let listPattern = patternChildren DefaultPatternList $ replicate 3 DefaultPatternWildcard
            listTerm elements =
              UPLC.Match
                ()
                (mkConstant @[Integer] () elements)
                ( Vector.fromList
                    [ (listPattern, constantInteger 0)
                    , (DefaultPatternWildcard, constantInteger 1)
                    ]
                )
        assertBothEvaluateTo (constantInteger 1) $ listTerm [1, 2]
        assertBothEvaluateTo (constantInteger 1) $ listTerm [1, 2, 3, 4]
        assertBothEvaluateTo (constantInteger 0) $ listTerm [1, 2, 3]
        patternBudget (listTerm [1, 2]) @?= ExBudget 5 0
        patternBudget (listTerm [1, 2, 3, 4]) @?= ExBudget 6 0
        patternBudget (listTerm [1, 2, 3]) @?= ExBudget 5 0
    , testCase "production and steppable CEK agree on Match and Apply budgets" $ do
        let assertParity wanted term =
              steppableStepBudget wanted term @?= stepBudget wanted term
            assertPatternParity term =
              steppablePatternBudget term @?= patternBudget term
            matchTerm =
              UPLC.Match
                ()
                captureScrutinee
                (Vector.singleton (capturePattern, captureHandler))
            shortBuiltinMatch =
              UPLC.Match
                ()
                (mkConstant @[Integer] () [])
                ( Vector.fromList
                    [
                      ( patternChildren DefaultPatternList $ replicate 8 DefaultPatternWildcard
                      , constantInteger 0
                      )
                    , (DefaultPatternWildcard, constantInteger 1)
                    ]
                )
        assertPatternParity captureTerm
        assertParity Cek.BApply captureTerm
        assertPatternParity matchTerm
        assertParity Cek.BApply matchTerm
        assertBothEvaluateTo (constantInteger 1) shortBuiltinMatch
        assertPatternParity shortBuiltinMatch
    , testCase "direct pattern spending cannot pollute the BConst counter" $ do
        let term = matchSingle DefaultPatternWildcard (constantInteger 1) (constantInteger 0)
        assertBothEvaluateTo (constantInteger 1) term
        stepBudget Cek.BConst term @?= ExBudget 2 0
        steppableStepBudget Cek.BConst term @?= ExBudget 2 0
    ]
