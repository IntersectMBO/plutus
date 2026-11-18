-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Evaluation.Machines
  ( test_machines
  , test_budget
  , test_tallying
  , test_NumberOfStepCounters
  ) where

import PlutusPrelude

import UntypedPlutusCore
import UntypedPlutusCore.Evaluation.Machine.Cek as Cek
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (NumberOfStepCounters)
import UntypedPlutusCore.Evaluation.Machine.SteppableCek qualified as SCek

import PlutusCore qualified as Plc
import PlutusCore.Builtin
import PlutusCore.Compiler.Erase
import PlutusCore.Data qualified as Data
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..), ExRestrictingBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetStream (ExBudgetStream (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as Plc
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.FsTree
import PlutusCore.Generators.Hedgehog.Interesting
import PlutusCore.MkPlc
import PlutusCore.Pretty

import PlutusCore.Examples.Builtins
import PlutusCore.StdLib.Data.Nat qualified as Plc
import PlutusCore.StdLib.Meta
import PlutusCore.StdLib.Meta.Data.Function (etaExpand)

import Data.Proxy (Proxy (..))
import Data.Text (Text)
import Data.Vector qualified as Vector
import GHC.Exts (fromString)
import GHC.Ix
import GHC.TypeNats (natVal)
import Hedgehog hiding (Size, Var, eval)
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.Golden
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

testMachine
  :: (uni ~ DefaultUni, fun ~ DefaultFun, PrettyPlc structural)
  => String
  -> ( Term Name uni fun ()
       -> Either
            (EvaluationException structural operational (Term Name uni fun ()))
            (Term Name uni fun ())
     )
  -> TestTree
testMachine machine eval =
  testGroup machine $ fromInterestingTermGens $ \name genTermWithTbv ->
    testPropertyNamed name (fromString name) . withTests 99 . property $ do
      TermWith term val <- forAllWith mempty genTermWithTbv
      let resExp = makeKnownOrFail @_ @(Plc.Term TyName Name DefaultUni DefaultFun ()) val
      case splitStructuralOperational . eval $ eraseTerm term of
        Left err -> fail $ show err
        Right resAct -> resAct === fmap eraseTerm resExp

test_machines :: TestTree
test_machines =
  testGroup
    "machines"
    [ testMachine "CEK" $ Cek.evaluateCekNoEmit Plc.defaultCekParametersForTesting
    , testMachine "SteppableCEK" $ SCek.evaluateCekNoEmit Plc.defaultCekParametersForTesting
    , test_transitions
    , test_builtinBudgetOrder
    ]

-- A result must remain unevaluated until its entire budget has been spent. An exception
-- detects premature evaluation even when ordinary result-and-budget comparisons would pass.
test_builtinBudgetOrder :: TestTree
test_builtinBudgetOrder =
  testGroup
    "builtin budget before result"
    [ testCase (streamName ++ "/" ++ name) $ do
        let result = BuiltinCostedResult budgets (throw BuiltinErrorCall)
            runtime =
              if forced
                then BuiltinExpectForce result
                else BuiltinExpectArgument (const result)
            params =
              MachineParameters def $
                MachineVariantParameters
                  Plc.defaultCekMachineCostsForTesting
                  (BuiltinsRuntime $ const runtime)
            mode = restricting $ ExRestrictingBudget $ ExBudget 1000000 1000000
            report = Cek.runCekDeBruijn params mode logEmitter term
        case cekResultToEither $ _cekReportResult report of
          Left (ErrorWithCause (OperationalError (CekOutOfExError _)) _) -> pure ()
          other -> assertFailure $ "Expected budget exhaustion, got: " ++ displayPlc other
    | (streamName, budgets) <- streams
    , (name, term, forced) <- terms
    ]
  where
    excessive = ExBudget 1000000000000 1000000000000
    streams =
      [ ("single cost", ExBudgetLast excessive)
      , ("unevaluated cost tail", ExBudgetCons excessive $ throw BuiltinErrorCall)
      ]

    one :: Term NamedDeBruijn DefaultUni DefaultFun ()
    one = mkConstant () (1 :: Integer)
    builtin = Builtin () AddInteger
    terms =
      [ ("apply", Apply () builtin one, False)
      , ("force", Force () builtin, True)
      , ("apply under function", Apply () (Apply () builtin one) one, False)
      , ("force under function", Apply () (Force () builtin) one, True)
      , ("evaluated arguments", Case () (Constr () 0 [one, one]) $ Vector.singleton builtin, False)
      ]

-- The steppable machine provides an independent reference for changes to CEK transitions.
-- Returning a value directly and returning it through a builtin can take different optimized
-- paths. Both must preserve errors, logs and spending, including at budget boundaries.
test_transitions :: TestTree
test_transitions =
  testGroup "transition equivalence" $
    [ testTransition
        (contextName ++ "/" ++ producerName ++ "/" ++ valueName)
        (context (producer value))
    | (contextName, context) <- contexts
    , (producerName, producer) <- producers
    , (valueName, value) <- values
    ]
      ++ [testTransition "data matcher with evaluated arguments" dataMatcher]
  where
    integer :: Integer -> Term NamedDeBruijn DefaultUni DefaultFun ()
    integer = mkConstant ()

    lambda = LamAbs () (fakeNameDeBruijn $ DeBruijn 0)
    identity = lambda $ Var () (fakeNameDeBruijn $ DeBruijn 1)
    apps = foldl' (Apply ())

    values =
      [ ("constant", integer 7)
      , ("delay", Delay () $ integer 8)
      , ("delayed error", Delay () $ Error ())
      , ("lambda", identity)
      , ("lambda with error", lambda $ Error ())
      , ("partial builtin", Apply () (Builtin () AddInteger) $ integer 9)
      , ("polymorphic builtin", Builtin () IfThenElse)
      , ("constructor", Constr () 0 [integer 10])
      , ("empty constructor", Constr () 0 [])
      ]

    contexts =
      [ ("return", id)
      , ("force", Force ())
      , ("argument", Apply () $ lambda $ integer 11)
      , ("function", \t -> Apply () t $ integer 12)
      , ("last constructor field", \t -> Constr () 0 [t])
      , ("first constructor field", \t -> Constr () 0 [t, integer 13])
      , ("scrutinee", \t -> Case () t $ Vector.singleton identity)
      ,
        ( "evaluated arguments"
        , \t -> Case () (Constr () 0 [integer 16, integer 17]) $ Vector.singleton t
        )
      ,
        ( "native constant arguments"
        , \t -> Case () (mkConstant () (18 :: Integer, 19 :: Integer)) $ Vector.singleton t
        )
      ]

    producers =
      [ ("direct", id)
      ,
        ( "builtin result"
        , \v -> apps (Force () $ Builtin () IfThenElse) [mkConstant () True, v, v]
        )
      ,
        ( "logging builtin result"
        , \v -> apps (Force () $ Builtin () Trace) [mkConstant () (fromString "trace" :: Text), v]
        )
      ]

    -- The unused branches must stay delayed while chooseData consumes its six evaluated
    -- arguments. Forcing the selected branch also exercises a builtin returning a closure.
    dataMatcher =
      Force () $
        Case
          ()
          ( Constr
              ()
              0
              [ mkConstant () $ Data.List []
              , Delay () $ Error ()
              , Delay () $ Error ()
              , Delay () $ integer 42
              , Delay () $ Error ()
              , Delay () $ Error ()
              ]
          )
          (Vector.singleton $ Force () $ Builtin () ChooseData)

    testTransition :: TestName -> Term NamedDeBruijn DefaultUni DefaultFun () -> TestTree
    testTransition name term = testCase name $ do
      let run
            :: ExBudgetMode cost DefaultUni DefaultFun
            -> CekReport cost NamedDeBruijn DefaultUni DefaultFun
          run mode = Cek.runCekDeBruijn Plc.defaultCekParametersForTesting mode logEmitter term
          reference
            :: ExBudgetMode cost DefaultUni DefaultFun
            -> CekReport cost NamedDeBruijn DefaultUni DefaultFun
          reference mode =
            SCek.runCekDeBruijn Plc.defaultCekParametersForTesting mode logEmitter term
          report (CekReport result cost logs) = (cekResultToEither result, cost, logs)
          compareMode :: (Eq cost, Show cost) => ExBudgetMode cost DefaultUni DefaultFun -> IO ()
          compareMode mode = assertEqual name (report $ reference mode) (report $ run mode)
          CountingSt budget@(ExBudget cpu mem) = _cekReportCost $ run counting
      compareMode counting
      compareMode tallying
      for_ [ExBudget 0 0, budget, ExBudget (max 0 $ cpu - 1) mem, ExBudget cpu (max 0 $ mem - 1)] $
        compareMode . restricting . ExRestrictingBudget

testBudget
  :: (Ix fun, Show fun, Hashable fun, Pretty fun, Typeable fun)
  => BuiltinsRuntime fun (CekValue DefaultUni fun ())
  -> TestName
  -> Term Name DefaultUni fun ()
  -> TestNested
testBudget runtime name term =
  nestedGoldenVsText
    name
    ".uplc"
    ( render $
        prettyPlcReadable $
          runCekNoEmit
            ( MachineParameters def $
                MachineVariantParameters Plc.defaultCekMachineCostsForTesting runtime
            )
            Cek.tallying
            term
    )

bunchOfFibs :: PlcFolderContents DefaultUni DefaultFun
bunchOfFibs = FolderContents [treeFolderContents "Fib" $ map fibFile [1 .. 3]]
  where
    fibFile i = plcTermFile (show i) (naiveFib i)

{-| To check how a sequence of calls to a built-in @id@ affects budgeting when a (relatively)
big AST is threaded through them. -}
bunchOfIdNats :: PlcFolderContents DefaultUni ExtensionFun
bunchOfIdNats =
  FolderContents [treeFolderContents "IdNat" $ map idNatFile [0 :: Int, 3 .. 9]]
  where
    idNatFile i = plcTermFile (show i) (idNat id0 i)
    -- > id0 = foldNat {nat} succ zero
    id0 = mkIterAppNoAnn (tyInst () Plc.foldNat $ Plc.natTy) [Plc.succ, Plc.zero]

    idNat idN 0 = apply () idN $ metaIntegerToNat 10
    idNat idN n = idNat idN' (n - 1)
      where
        -- Intentionally not eta-expanding the call to @idN'@, so that it gets forced during
        -- evaluation, which causes @idN@ to get forced, which on the first iteration causes
        -- @id0@ to get forced, which gives us a sufficiently big AST.
        -- > idN' = id {nat -> nat} idN
        idN' = apply () (tyInst () (builtin () Id) $ Plc.TyFun () Plc.natTy Plc.natTy) idN

-- | Same as 'bunchOfIdNats' except uses the built-in @ifThenElse@.
bunchOfIfThenElseNats :: PlcFolderContents DefaultUni DefaultFun
bunchOfIfThenElseNats =
  FolderContents [treeFolderContents "IfThenElse" $ map ifThenElseNatFile [0 :: Int, 1 .. 5]]
  where
    ifThenElseNatFile i = plcTermFile (show i) (ifThenElseNat id0 i)
    -- > id0 = foldNat {nat} succ zero
    id0 = mkIterAppNoAnn (tyInst () Plc.foldNat Plc.natTy) [Plc.succ, Plc.zero]

    ifThenElseNat idN 0 = apply () idN $ metaIntegerToNat 10
    ifThenElseNat idN n = ifThenElseNat idN' (n - 1)
      where
        -- Eta-expanding @idN'@ so that all of the if-then-else-s don't get evaluated --
        -- only those that are on the actual execution path.
        -- > idN' = \(n : nat) -> ifThenElse {nat -> nat} ($(even n)) idN idN n
        idN' =
          etaExpand Plc.natTy $
            mkIterAppNoAnn
              (tyInst () (builtin () IfThenElse) $ Plc.TyFun () Plc.natTy Plc.natTy)
              [mkConstant () $ even n, idN, idN]

test_budget :: TestTree
test_budget =
  -- Error diffs are very big
  localOption (SizeCutoff 1000000)
    . runTestNested ["untyped-plutus-core", "test", "Evaluation", "Machines", "Budget"]
    $ concat
      [ folder Plc.defaultBuiltinsRuntimeForTesting bunchOfFibs
      , folder (toBuiltinsRuntime def ()) bunchOfIdNats
      , folder Plc.defaultBuiltinsRuntimeForTesting bunchOfIfThenElseNats
      ]
  where
    folder runtime =
      foldPlcFolderContents testNested mempty (\name -> testBudget runtime name . eraseTerm)

testTallying :: TestName -> Term Name DefaultUni DefaultFun () -> TestNested
testTallying name term =
  nestedGoldenVsText
    name
    ".uplc"
    (render $ prettyPlcReadable $ runCekNoEmit Plc.defaultCekParametersForTesting Cek.tallying term)

test_tallying :: TestTree
test_tallying =
  -- Error diffs are very big
  localOption (SizeCutoff 1000000)
    . runTestNested ["untyped-plutus-core", "test", "Evaluation", "Machines", "Tallying"]
    . foldPlcFolderContents testNested mempty (\name -> testTallying name . eraseTerm)
    $ bunchOfFibs

test_NumberOfStepCounters :: TestTree
test_NumberOfStepCounters =
  runTestNestedM ["untyped-plutus-core", "test", "Evaluation", "Machines"] $ do
    nestedGoldenVsDoc "NumberOfStepCounters" "" . pretty . natVal $ Proxy @NumberOfStepCounters
    nestedGoldenVsDoc "NumberOfStepCounters" "" . pretty . length $ enumerate @StepKind
