{-# LANGUAGE TypeApplications #-}
module DeBruijn.Scope (test_scope) where

import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Check.Scope as UPLC

import Control.Monad.Except
import Data.Bifunctor
import Data.Either
import DeBruijn.Common
import PlutusCore.Default
import PlutusCore.MkPlc
import Test.Tasty.Extras
import Test.Tasty.HUnit

-- Note: The point of these tests is that
-- binders with wrong indices and
-- variables with wrong indices (e.g. out of scope) will fail the scope-check pass.

-- TODO: add random AST/NEAT generation to test that
-- `(debruijnTerm >=> scopeCheck)` succeeds if `debruijnTerm` succeeds.

-- (lam x_0 x_1)
okId0 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
okId0 = lamAbs0 $ Var () $ DeBruijn 1

-- (lam x_99 x_1) , behaves the same as id
failId99 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failId99 = lamAbs99 $ Var () $ DeBruijn 1

-- (delay outVar)
failTop :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failTop = Delay () outVar

-- (lam x_0 outVar)
failBody0 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failBody0 = lamAbs0 outVar

-- (lam x_99 outVar)
failBody99 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failBody99 = lamAbs99 outVar

-- [(lam x (lam y x)) (con integer 1) (lam0 outVar)]
failConst :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failConst = mkIterApp () constFun [true, failBody0]

-- [(lam x (lam y x)) (con bool true) (lam99 x_1)]
failConst99 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failConst99 = mkIterApp () constFun [true, failId99]

-- [(force (builtin ifThenElse)) (con bool True) (lam0 x1) (lam99 outVar)]
failITE :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failITE = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ mkConstant @Bool () True -- pred
         , okId0 -- then
         , failBody99 -- else
         ]

failTop0 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failTop0 = Var () (DeBruijn 0)

failTop1 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failTop1 = Var () (DeBruijn 1)

failApply01 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failApply01 = timesT 5 (Apply () (timesT 10 delayforce failTop0)) (timesT 20 delayforce failTop1)

-- (lam0 ...n.... (Var n+1))
okDeep0 :: Index -> UPLC.Term DeBruijn DefaultUni DefaultFun ()
okDeep0 n = timesT n lamAbs0 $ Var () $ DeBruijn n

-- (lam9999 ...n.... (Var n+1))
failDeep99 :: Index -> Term DeBruijn DefaultUni DefaultFun ()
failDeep99 n = timesT n lamAbs99 $ Var () $ DeBruijn n

-- (lam ...n.... (Var n+2))
failDeep :: Index -> Term DeBruijn DefaultUni DefaultFun ()
failDeep n = timesT n lamAbs0 $ Var () $ DeBruijn $ n+1

-- (lam0 ...n.... lam0 ...n.... (Var n+n+1))
okMix :: Index -> Term DeBruijn DefaultUni DefaultFun ()
okMix n = timesT n lamAbs0 $ timesT n lamAbs0 $ Var () $ DeBruijn $ n+n

-- (lam0 ...n.... lam99 ...n.... (Var n+n+1))
failMix1 :: Index -> Term DeBruijn DefaultUni DefaultFun ()
failMix1 n = timesT n lamAbs0 $ timesT n lamAbs99 $ Var () $ DeBruijn $ n+n

-- (lam0 ...n.... lam99 ...n.... (Var n+n+2))
failMix2 :: Index -> Term DeBruijn DefaultUni DefaultFun ()
failMix2 n = timesT n lamAbs0 $ timesT n lamAbs99 $ Var () $ DeBruijn $ n+n+1

testsOk :: [(String, UPLC.Term DeBruijn DefaultUni DefaultFun ())]
testsOk =
    [("okId0", okId0)
    ,("okDeep0", okDeep0 10)
    ,("okMix", okMix 10)
    ]

testsFail :: [(String, UPLC.Term DeBruijn DefaultUni DefaultFun ())]
testsFail =
    [("failTop", failTop)
    ,("failId99", failId99)
    ,("failConst", failConst)
    ,("failConst99", failConst99)
    ,("failBody0", failBody0)
    ,("failBody99", failBody99)
    ,("failITE", failITE)
    ,("failDeep", failDeep 10)
    ,("failDeep99", failDeep99 10)
    ,("failMix1", failMix1 10)
    ,("failMix2", failMix2 10)
    ,("failTop0", failTop0)
    ,("failTop1", failTop1)
    ,("failApply01", failApply01)
    ]


test_scope :: TestNested
test_scope = testNested "Scope" $ pure . uncurry testCase <$>
                 (second testPasses <$> testsOk)
               <> (second testThrows <$> testsFail)
    where
      testPasses t =
          (isRight $ runExcept @FreeVariableError $ checkScope t)
          @? "scope checking failed unexpectedly"
      testThrows t =
          (isLeft $ runExcept @FreeVariableError $ checkScope t)
          @? "scope checking passed unexpectedly"
