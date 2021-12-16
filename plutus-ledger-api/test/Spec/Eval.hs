{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
module Spec.Eval (tests) where

import Codec.Serialise qualified as CBOR
import Common
import Control.Monad.Except
import Data.ByteString.Lazy qualified as BSL
import Data.ByteString.Short qualified as BSS
import Data.Either
import Data.Maybe
import Plutus.V1.Ledger.Api as Api
import Plutus.V1.Ledger.Scripts as Scripts
import PlutusCore qualified as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.MkPlc
import Test.Tasty
import Test.Tasty.HUnit
import UntypedPlutusCore as UPLC

{- NOTE [Direct UPLC code]
For this test-suite we write the programs directly in the UPLC AST,
bypassing the GHC typechecker & compiler, the PIR typechecker & compiler and the PLC typechecker.
The reason is that users can submit such hand-crafted code, and we want to test how it behaves.
Because this is part of our API, we have to be careful not to change the behaviour of even weird untypeable programs.
-}

-- (delay outOfScope)
-- Interesting example because it is a delayed value, which would definitely blow up if forced.
-- The evaluation result (success or failure) depends on how the machine handles `dischargeCekValue`.
outDelay :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outDelay = Delay () outOfScope

-- (lam x outOfScope)
-- Interesting example because it is a lambda (delayed) value, which would definitely blow up if applied.
-- The evaluation result (success or failure) depends on how the machine handles `dischargeCekValue`.
outLam :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outLam = mkLam outOfScope

-- [(lam x (lam y x)) (con bool True) (lam x outOfScope)]
-- Interesting example because it is a `const x y` where x is a value and y is out-of-scope.
-- The evaluation result (success or failure) depends on how the machine
-- ignores  the irrelevant to the computation) part of the environment.
outConst :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outConst = mkIterApp () (mkLam $ mkLam $ Var () $ DeBruijn 2) [true, outLam]

-- [(force (builtin ifThenElse)) (con bool True) (con bool True) outOfScope]
-- Both branches are evaluate *before* the predicate, so it is clear that this should fail in every case.
outITEStrict :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outITEStrict = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ true -- pred
         , true -- then
         , outOfScope -- else
         ]
-- [(force (builtin ifThenElse)) (con bool True) (delay true) (delay outOfScope)]
-- The branches are *lazy*. The evaluation result (success or failure) depends on how the machine
-- ignores  the irrelevant to the computation) part of the environment.
outITELazy :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outITELazy = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ true -- pred
         , Delay () true -- then
         , Delay () outOfScope -- else
         ]

-- [(force (builtin ifThenElse)) (con bool True) (con bool  True) (con unit ())]
-- Note that the branches have **different** types.
illITEStrict :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illITEStrict = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ true -- pred
         , true -- then
         , unit -- else
         ]

-- [(force (builtin ifThenElse)) (con bool True) (lam x (con bool  True)) (lam x (con unit ()))]
-- The branches are *lazy*. Note that the branches have **different** types.
illITELazy :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illITELazy = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ true -- pred
         , mkLam true -- then
         , Delay () true -- else
         ]
-- [(builtin addInteger) (con integer 1) (con unit ())]
-- Interesting because it involves a runtime type-error of a builtin.
illAdd :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illAdd = mkIterApp ()
         (Builtin () AddInteger)
         [ one
         , unit
         ]

-- [(builtin addInteger) (con integer 1) (con integer 1) (con integer 1)]
-- Interesting because it involves a (builtin) over-saturation type-error, which the machine can recognize.
illOverSat :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illOverSat = mkIterApp ()
             (Builtin () AddInteger)
             [ one
             , one
             , one]

-- [(lam x x) (con integer 1) (con integer 1)]
-- Interesting because it involves a (lambda) over-saturation type-error, which the machine can recognize.
illOverApp :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illOverApp = mkIterApp ()
             (mkLam $ Var () $ DeBruijn 1) -- id
             [ one
             , one
             ]

testOffline :: TestNested
testOffline = pure . testCase "offline" $ do
    eval outDelay @?= False
    eval outLam @?= False
    eval outConst @?= False
    eval outITEStrict @?= False
    eval outITELazy @?= False
    eval illAdd @?= False
    eval illOverSat @?= False
    eval illOverApp @?= False
    -- some ill-typed expressions cannot be caught by the machine
    eval illITEStrict @?= True
    eval illITELazy @?= True
  where
      eval :: UPLC.Term DeBruijn DefaultUni DefaultFun () -> Bool
      eval = isRight . runExcept . evaluateScript . Script . mkProg


{-| Evaluates scripts as they will be evaluated on-chain, by using the evaluation function we provide for the ledger.
Notably, this goes via serializing and deserializing the program, so we can see any errors that might arise from that.
Currently, this includes de Bruijn conversion, but this will go away once we change the evaluator to operate
on de Bruijn indices directly.
currently behaves similar to offlineEvalExternal, because any out-of-scope errors will be caught by
the undebruinification step of mkTermToEvaluate. Subject to change by direct debruijn branch.
-}
testOnline :: TestNested
testOnline = pure . testCase "online" $ do
    eval outDelay @?= False
    eval outLam @?= False
    eval outConst @?= False
    eval outITEStrict @?= False
    eval outITELazy @?= False
    eval illAdd @?= False
    eval illOverSat @?= False
    eval illOverApp @?= False
    -- some ill-typed expressions cannot be caught by the machine
    eval illITEStrict @?= True
    eval illITELazy @?= True
  where
      eval :: UPLC.Term DeBruijn DefaultUni DefaultFun () -> Bool
      eval t =
          -- handcraft a serialized script
          let s :: SerializedScript = BSS.toShort . BSL.toStrict . CBOR.serialise $ Script $ mkProg t
          in isRight $ snd $ Api.evaluateScriptRestricting Quiet (fromJust defaultCostModelParams) (unExRestrictingBudget enormousBudget) s []

tests :: TestTree
tests = runTestNestedIn ["plutus-ledger-api"] $
          testNested "eval"
            [ testOffline
            , testOnline
            -- TODO: implement testOfflineInternal for cek-debruijn branch using Cek.Internal, to show that also no out-of-scope will be caught
            ]


mkProg :: UPLC.Term DeBruijn DefaultUni DefaultFun () ->  UPLC.Program DeBruijn DefaultUni DefaultFun ()
mkProg = Program () $ PLC.defaultVersion ()

true :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
true = mkConstant @Bool () True

one :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
one = mkConstant @Integer () 1

unit :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
unit = mkConstant @() () ()

-- a helper to intro a lam, debruijn are always 0-indexed
mkLam :: (t ~ UPLC.Term DeBruijn DefaultUni DefaultFun ()) => t -> t
mkLam = LamAbs () (DeBruijn 0)

-- a sufficient large debruijn index for testing
outOfScope :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outOfScope = Var () (DeBruijn 9999999)

