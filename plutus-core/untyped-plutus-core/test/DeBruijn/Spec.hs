{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
module DeBruijn.Spec (test_debruijn) where

import Common
import Control.Monad.Except
import Control.Monad.State
import Data.Semigroup
import PlutusCore (defaultVersion)
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.MkPlc
import PlutusCore.Pretty
import PlutusCore.Quote
import Test.Tasty
import UntypedPlutusCore as UPLC

-- Note: This tests two things during undebruijnification:
-- 1) binders with wrong indices will be undebruinified successfully
-- 2) variables with wrong indices (e.g. out of scope) will fail to undebruijnify

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

-- (lam0 ...n.... (Var n+1))
okDeep0 :: Index -> UPLC.Term DeBruijn DefaultUni DefaultFun ()
okDeep0 n = timesAbs n lamAbs0 $ Var () $ DeBruijn n

-- (lam9999 ...n.... (Var n+1))
okDeep99 :: Index -> Term DeBruijn DefaultUni DefaultFun ()
okDeep99 n = timesAbs n lamAbs99 $ Var () $ DeBruijn n

-- (lam ...n.... (Var n+2))
failDeep :: Index -> Term DeBruijn DefaultUni DefaultFun ()
failDeep n = timesAbs n lamAbs0 $ Var () $ DeBruijn $ n+1

-- (lam0 ...n.... lam99 ...n.... (Var n+n+1))
okMix1 :: Index -> Term DeBruijn DefaultUni DefaultFun ()
okMix1 n = timesAbs n lamAbs0 $ timesAbs n lamAbs99 $ Var () $ DeBruijn $ n+n

-- (lam99 ...n.... lam0 ...n.... (Var n+n+1))
okMix2 :: Index -> Term DeBruijn DefaultUni DefaultFun ()
okMix2 n = timesAbs n lamAbs99 $ timesAbs n lamAbs0 $ Var () $ DeBruijn $ n+n

-- (lam0 ...n.... lam99 ...n.... (Var n+n+2))
failMix :: Index -> Term DeBruijn DefaultUni DefaultFun ()
failMix n = timesAbs n lamAbs0 $ timesAbs n lamAbs99 $ Var () $ DeBruijn $ n+n+1

test_debruijn :: TestTree
test_debruijn = runTestNestedIn ["untyped-plutus-core","test"] $
                  testNested "DeBruijn"
                   [testNested "Golden"
                    [testNested "Strict" $
                      fmap (\ (n,t) -> nestedGoldenVsDoc n $ actThrow t) tests
                    ,testNested "Graceful" $
                      fmap (\ (n,t) -> nestedGoldenVsDoc n $ actGrace t) testsGrace
                    ]
                   ]
  where
    actThrow = prettyPlcClassicDebug . runExcept @(Error DefaultUni DefaultFun ()) . runQuoteT . progTerm unDeBruijnTerm . mkProg

    actGrace = prettyPlcClassicDebug . runExcept @(Error DefaultUni DefaultFun ())
                . runQuoteT
                . flip evalStateT mempty
                . progTerm (unDeBruijnTermWith freeIndexAsConsistentLevel) . mkProg

    mkProg = Program () (defaultVersion ()) . termMapNames fakeNameDeBruijn

    tests = [("okId0", okId0)
            ,("okId99", okId99)
            ,("failTop", failTop)
            ,("failBody0", failBody0)
            ,("failBody99", failBody99)
            ,("okConst", okConst)
            ,("failConst", failConst)
            ,("failITE", failITE)
            ,("okDeep0", okDeep0 10)
            ,("okDeep99", okDeep99 10)
            ,("failDeep", failDeep 10)
            ,("okMix1", okMix1 10)
            ,("okMix2", okMix2 10)
            ,("failMix", failMix 10)
            ]

    testsGrace = [("graceDeep", failDeep 5)
                  ,("graceTop", failTop)
                  ,("graceConst", failConst)
                  ,("graceElaborate", graceElaborate)
                  ]


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

-- HELPERS

-- a big debruijn index for testing.
-- the actual number does not matter, as long as it is sufficiently large to not interfere with the rest of the test code.
ix99 :: DeBruijn
ix99 = DeBruijn 999999

-- An out-of-scope variable in these tests.
outVar :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outVar = Var () ix99

true :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
true = mkConstant @Bool () True

-- A helper that just places index 0 to the binder (the only "reasonable" index for the binders)
lamAbs0 :: (t ~ UPLC.Term DeBruijn DefaultUni DefaultFun ()) => t -> t
lamAbs0 = LamAbs () (DeBruijn 0)

-- A helper that constructs a lamabs with the binder having a nonsensical index.
-- See NOTE: [DeBruijn indices of Binders]
lamAbs99 :: (t ~ UPLC.Term DeBruijn DefaultUni DefaultFun ()) => t -> t
lamAbs99 = LamAbs () ix99

constFun :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
constFun = lamAbs0 $ lamAbs0 $ Var () $ DeBruijn 2

timesAbs :: Index -> (a -> a)  -> a -> a
timesAbs n = appEndo . stimes n . Endo

