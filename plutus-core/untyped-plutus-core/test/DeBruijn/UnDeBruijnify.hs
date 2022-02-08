{-# LANGUAGE TypeApplications #-}
module DeBruijn.UnDeBruijnify (test_undebruijnify) where

import Control.Monad.Except
import Control.Monad.State
import DeBruijn.Common
import PlutusCore (defaultVersion)
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.MkPlc
import PlutusCore.Pretty
import PlutusCore.Quote
import Test.Tasty.Extras
import UntypedPlutusCore as UPLC

-- Note: The point of these tests is that
-- binders with wrong indices will be undebruinified successfully, whereas
-- variables with wrong indices (e.g. out of scope) will fail.

-- (lam x_0 x_1)
okId0 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
okId0 = lamAbs0 $ Var () $ DeBruijn 1

-- (lam x_99 x_1) , behaves the same as id
okId99 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
okId99 = lamAbs99 $ Var () $ DeBruijn 1

-- (delay outVar)
failTop :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failTop = Delay () outVar

-- (lam x_0 outVar)
failBody0 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failBody0 = lamAbs0 outVar

-- (lam x_99 outVar)
failBody99 :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failBody99 = lamAbs99 outVar

-- [(lam x (lam y x)) (con bool true) (lam99 x_1)]
okConst :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
okConst = mkIterApp () constFun [true, okId99]

-- [(lam x (lam y x)) (con integer 1) (lam0 outVar)]
failConst :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
failConst = mkIterApp () constFun [true, failBody0]

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
okDeep99 :: Index -> Term DeBruijn DefaultUni DefaultFun ()
okDeep99 n = timesT n lamAbs99 $ Var () $ DeBruijn n

-- (lam ...n.... (Var n+2))
failDeep :: Index -> Term DeBruijn DefaultUni DefaultFun ()
failDeep n = timesT n lamAbs0 $ Var () $ DeBruijn $ n+1

-- (lam0 ...n.... lam99 ...n.... (Var n+n+1))
okMix1 :: Index -> Term DeBruijn DefaultUni DefaultFun ()
okMix1 n = timesT n lamAbs0 $ timesT n lamAbs99 $ Var () $ DeBruijn $ n+n

-- (lam99 ...n.... lam0 ...n.... (Var n+n+1))
okMix2 :: Index -> Term DeBruijn DefaultUni DefaultFun ()
okMix2 n = timesT n lamAbs99 $ timesT n lamAbs0 $ Var () $ DeBruijn $ n+n

-- (lam0 ...n.... lam99 ...n.... (Var n+n+2))
failMix :: Index -> Term DeBruijn DefaultUni DefaultFun ()
failMix n = timesT n lamAbs0 $ timesT n lamAbs99 $ Var () $ DeBruijn $ n+n+1

-- (lam0 [2 1 4 (lam99 [1 4 3 5])])
graceElaborate :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
graceElaborate = lamAbs0 $
    mkIterApp () (d 2)
      [
        d 1
      , d 4
      , lamAbs99 (mkIterApp () (d 1)
                 [
                   d 4
                 , d 3
                 , d 5
                 ]
                 )
      ]
 where
   d = Var () . DeBruijn

testsOk :: [(String, UPLC.Term DeBruijn DefaultUni DefaultFun ())]
testsOk =
    [("okId0", okId0)
    ,("okId99", okId99)
    ,("okConst", okConst)
    ,("okDeep0", okDeep0 10)
    ,("okDeep99", okDeep99 10)
    ,("okMix1", okMix1 10)
    ,("okMix2", okMix2 10)
    ]

testsFail :: [(String, UPLC.Term DeBruijn DefaultUni DefaultFun ())]
testsFail =
    [("failTop", failTop)
    ,("failBody0", failBody0)
    ,("failBody99", failBody99)
    ,("failConst", failConst)
    ,("failITE", failITE)
    ,("failDeep", failDeep 10)
    ,("failMix", failMix 10)
    ,("failTop0", failTop0)
    ,("failTop1", failTop1)
    ,("failApply01", failApply01)
    ]

testsGrace :: [(String, UPLC.Term DeBruijn DefaultUni DefaultFun ())]
testsGrace =
    [("graceDeep", failDeep 5)
    ,("graceTop", failTop)
    ,("graceConst", failConst)
    ,("graceElaborate", graceElaborate)
    ]

test_undebruijnify :: TestNested
test_undebruijnify = testNested "Golden"
                    [testNested "Strict" $
                      (\ (n,t) -> nestedGoldenVsDoc n $ actThrow t) <$> (testsFail <> testsOk)
                    ,testNested "Graceful" $
                      (\ (n,t) -> nestedGoldenVsDoc n $ actGrace t) <$> testsGrace
                    ]
  where
    actThrow = prettyPlcClassicDebug . runExcept @(Error DefaultUni DefaultFun ()) . runQuoteT . progTerm unDeBruijnTerm . mkProg
    actGrace = prettyPlcClassicDebug . runExcept @(Error DefaultUni DefaultFun ())
                . runQuoteT
                . flip evalStateT mempty
                . progTerm (unDeBruijnTermWith freeIndexAsConsistentLevel) . mkProg

    mkProg = Program () (defaultVersion ()) . termMapNames fakeNameDeBruijn






