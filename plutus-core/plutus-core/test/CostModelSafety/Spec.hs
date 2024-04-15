{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

{- | Tests to make sure that all of the CEK costs are positive and that no
builtins have a costing function which is identically zero.  During the
implementation of a new builtin it may be necessary to add a temporary costing
function. It's tempting to make such a function return 0 for all inputs, but
this might allow the builtin to be used for free on a testnet (for example)
which might be confusing. We try to encourage the use of a default costing
function which is maximally expensive, but the implementer might miss that.
It's still possible to provide a costing function which is unrealistically
cheap, but it would be difficult to spot that automatically.  Here we check that
the costing functions for each builtin are nonzero at a single point, and we do
this by running the function with a list of small arguments.  For CPU costs we
actually check that the cost is at least 1000 ExCPU and for memory costs we
check that the cost is strictly positive. -}

module CostModelSafety.Spec (test_costModelSafety)
where

import PlutusCore (DefaultFun, DefaultUni)
import PlutusCore qualified as PLC
import PlutusCore.Builtin
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data (Data (..))
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (ExBudget))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModel,
                                                          defaultCekMachineCosts)
import PlutusCore.Evaluation.Machine.ExBudgetStream (sumExBudgetStream)
import PlutusCore.Evaluation.Machine.ExMemoryUsage (LiteralByteSize)
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts,
                                                                 CekMachineCostsBase (..))

import Data.ByteString qualified as BS
import Data.Functor.Identity (Identity (..))
import Data.Kind qualified as GHC (Type)
import Data.List.Extra (enumerate)
import Data.Text (Text)
import Data.Word (Word8)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)
import Type.Reflection (TypeRep, eqTypeRep, pattern App, typeRep, (:~~:) (..))

-- Machine costs
checkBudget :: Identity ExBudget  -> IO ()
checkBudget (Identity (ExBudget cpu mem)) = do
  assertBool "exBudgetCPU  <= 0 in CEK machine costs" $ cpu > 0
  assertBool "exBudgetMemory <= 0 in CEK machine costs" $ mem > 0

-- Check that the machine costs are all strictly positive.  All of the fields are matched explicitly
-- to make sure that we don't forget any new ones that get added.
testMachineCostModel :: CekMachineCosts -> IO ()
testMachineCostModel (
  CekMachineCostsBase
    cekStartupBudget
    cekVarBudget
    cekConstBudget
    cekLamBudget
    cekDelayBudget
    cekForceBudget
    cekApplyBudget
    cekBuiltinBudget
    cekConstrBudget
    cekCaseBudget
  ) = do
    checkBudget cekStartupBudget
    checkBudget cekVarBudget
    checkBudget cekConstBudget
    checkBudget cekLamBudget
    checkBudget cekDelayBudget
    checkBudget cekForceBudget
    checkBudget cekApplyBudget
    checkBudget cekBuiltinBudget
    checkBudget cekConstrBudget
    checkBudget cekCaseBudget

-- Builtin costs

{- Much of the code here is based on Evaluation.Spec and
   PlutusCore.Generators.Hedgehog.Builtin.  The tests are complicated by the
   fact that We can't just read the models from `builtinCostModels.json` and
   check them since the actual models are defined by calls to `toBuiltinMeaning`
   in PlutusCore.Default.Builtins and those are free to supply their own costing
   functions and ignore the definitions in the JSON file.  The costing functions
   end up in the `BuiltinMeanings` and we can't access them directly and feed
   them suitable input sizes: instead we have to manufacture terms containing
   constants of the desired sizes and feed them to the denotation of the
   builtin.  The evaluation cost is calculated before the function is evaluated,
   so we still get sensible costs even if we get an evaluation failure (eg, due
   to division by zero).
-}

data SomeConst uni = forall a. uni `HasTermLevel` a => SomeConst a

smallConstant :: forall (a :: GHC.Type). TypeRep a -> SomeConst DefaultUni
smallConstant tr
    | Just HRefl <- eqTypeRep tr (typeRep @()) = SomeConst ()
    | Just HRefl <- eqTypeRep tr (typeRep @Integer) = SomeConst (0 :: Integer)
    | Just HRefl <- eqTypeRep tr (typeRep @Int) = SomeConst (0 :: Integer)
    | Just HRefl <- eqTypeRep tr (typeRep @Word8) = SomeConst (0 :: Integer)
    | Just HRefl <- eqTypeRep tr (typeRep @LiteralByteSize) = SomeConst (0 :: Integer)
    | Just HRefl <- eqTypeRep tr (typeRep @Bool) = SomeConst False
    | Just HRefl <- eqTypeRep tr (typeRep @BS.ByteString) = SomeConst $ BS.pack []
    | Just HRefl <- eqTypeRep tr (typeRep @Text) = SomeConst ("" :: Text)
    | Just HRefl <- eqTypeRep tr (typeRep @Data) = SomeConst $ I 0
    | Just HRefl <- eqTypeRep tr (typeRep @BLS12_381.G1.Element) =
                    SomeConst $ BLS12_381.G1.offchain_zero
    | Just HRefl <- eqTypeRep tr (typeRep @BLS12_381.G2.Element) =
                    SomeConst $ BLS12_381.G2.offchain_zero
    | Just HRefl <- eqTypeRep tr (typeRep @BLS12_381.Pairing.MlResult) =
                    SomeConst $ BLS12_381.Pairing.millerLoop
                                  BLS12_381.G1.offchain_zero BLS12_381.G2.offchain_zero
    | trPair `App` tr1 `App` tr2 <- tr
    , Just HRefl <- eqTypeRep trPair (typeRep @(,)) =
        case (smallConstant tr1, smallConstant tr2) of
            (SomeConst c1, SomeConst c2) -> SomeConst (c1, c2)
    | trList `App` trElem <- tr
    , Just HRefl <- eqTypeRep trList (typeRep @[]) =
        case smallConstant trElem of
          SomeConst c -> SomeConst ([] `asTypeOf` [c])
    | trSomeConstant `App` _ `App` trEl <- tr
    , Just HRefl <- eqTypeRep trSomeConstant (typeRep @SomeConstant) =
        smallConstant trEl
    | trOpaque `App` _ `App` trEl <- tr
    , Just HRefl <- eqTypeRep trOpaque (typeRep @Opaque) =
        smallConstant trEl
    | trTyVarRep `App` _ <- tr
    , Just HRefl <- eqTypeRep trTyVarRep (typeRep @(TyVarRep @GHC.Type)) =
        -- In the current implementation, all type variables are instantiated
        -- to `Integer` (TODO: change this?).
        smallConstant $ typeRep @Integer
    | otherwise = error $
        "smallConstant: I don't know how to generate constants of type " <> show tr

type Term = PLC.Term PLC.TyName PLC.Name DefaultUni DefaultFun ()

type family Head a where
    Head (x ': xs) = x

-- | Generate value arguments to a builtin function based on its `TypeScheme`.
genArgs
  :: BuiltinSemanticsVariant DefaultFun
  -> DefaultFun
  -> [Term]
genArgs semvar bn = case meaning of
    BuiltinMeaning tySch _ _ -> go tySch
      where
        go :: forall args res. TypeScheme Term args res -> [Term]
        go = \case
            TypeSchemeResult    -> []
            TypeSchemeArrow sch ->
              case smallConstant (typeRep @(Head args)) of
                SomeConst x -> (PLC.Constant () $ PLC.someValue x) : go sch
            TypeSchemeAll _ sch -> go sch
  where
    meaning :: BuiltinMeaning Term (CostingPart DefaultUni DefaultFun)
    meaning = toBuiltinMeaning semvar bn

testCosts
  :: BuiltinSemanticsVariant DefaultFun
  -> BuiltinsRuntime DefaultFun Term
  -> DefaultFun
  -> IO ()
testCosts semvar runtimes bn =
  let args0 = genArgs semvar bn
      runtime0 = lookupBuiltin bn runtimes

      eval :: [Term] -> BuiltinRuntime Term -> ExBudget
      eval [] (BuiltinCostedResult budgetStream _) = sumExBudgetStream budgetStream
      eval (arg : args) (BuiltinExpectArgument toRuntime) =
        eval args (toRuntime arg)
      eval args (BuiltinExpectForce runtime) =
        eval args runtime
      eval _ _ =
        error $ "Wrong number of args for builtin " <> show bn <> ": " <> show args0

      ExBudget cpuUsage memUsage = eval args0 runtime0
  in do
    -- Every builtin is expected to have a CPU cost of at least 1000 ExCPU (~ 1
    -- ns).  There's code in models.R which is supposed to ensure this.
    assertBool ("CPU cost < 1000 in " ++ show bn) $ cpuUsage >= 1000
    -- Some memory usage functions return 0 for inputs of size zero, but this
    -- should be OK since there should never be any inputs of size zero.
    assertBool ("Memory usage <= 0 in " ++ show bn) $ memUsage > 0

testBuiltinCostModel :: BuiltinSemanticsVariant DefaultFun -> TestTree
testBuiltinCostModel semvar =
  let builtins = enumerate @DefaultFun
      runtimes = toBuiltinsRuntime semvar defaultBuiltinCostModel
  in testCase ("Built-in cost model for " ++ show semvar) $
      mapM_ (testCosts semvar runtimes) builtins

test_costModelSafety :: TestTree
test_costModelSafety =
  testGroup "Default cost model safety test"
  (
  (testCase "Machine costs" $ testMachineCostModel defaultCekMachineCosts) :
    (fmap testBuiltinCostModel $ enumerate @(BuiltinSemanticsVariant DefaultFun))
  )
