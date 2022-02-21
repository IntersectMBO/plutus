{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}

module Evaluation.FreeVars
    ( test_freevars
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.DeBruijnEnv as Env
import Data.Either
import PlutusCore qualified as PLC
import PlutusCore.Default
import PlutusCore.MkPlc
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

-- TODO: share examples with plutus-ledger-api:Spec.Eval

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
-- Note that the branches have **different** types. The machine cannot catch such a type error.
illITEStrict :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
illITEStrict = mkIterApp ()
         (Force () (Builtin () IfThenElse))
         [ true -- pred
         , true -- then
         , unit -- else
         ]

-- [(force (builtin ifThenElse)) (con bool True) (lam x (con bool  True)) (lam x (con unit ()))]
-- The branches are *lazy*. Note that the branches have **different** types. The machine cannot catch such a type error.
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

test_freevars :: TestTree
test_freevars = testGroup "FreeVars" [ testCekInternalFree
                                     , testDischargeFree
                                     ]

true :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
true = mkConstant @Bool () True

one :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
one = mkConstant @Integer () 1

unit :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
unit = mkConstant @() () ()

-- a helper to intro a lam, debruijn binders are always 0-indexed
mkLam :: (t ~ UPLC.Term DeBruijn DefaultUni DefaultFun ()) => t -> t
mkLam = LamAbs () (DeBruijn 0)

-- a sufficient large debruijn index for testing
outOfScope :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outOfScope = Var () (DeBruijn 9999999)


-- | Test the behaviour of Cek evaluator module *directly*
-- by using the Internal module, thus bypassing any prior term conformance checks, e.g.
-- that the term is closed (no free variables).
testCekInternalFree :: TestTree
testCekInternalFree = testCase "cekInternal" $ do
    eval outDelay @?= True
    eval outLam @?= True
    eval outConst @?= True
    eval outITEStrict @?= False
    eval outITELazy @?= True
    eval illITEStrict @?= True
    eval illITELazy @?= True
    eval illAdd @?= False
    eval illOverSat @?= False
    eval illOverApp @?= False
  where
      eval = isRight . fstT . runCekDeBruijn PLC.defaultCekParameters counting noEmitter
             . termMapNames fakeNameDeBruijn
      fstT (x,_,_) =x

-- | Test the behaviour of discharge function against open terms (containing free variables)
-- by manually constructing CekValue's and Cek Environment's.
testDischargeFree :: TestTree
testDischargeFree = testCase "discharge" $ do
    -- free variable is left alone
    -- dis( empty |- (delay (\.9999)) ) === (delay (\.9999))
    dis (VDelay (n outLam) empty) @?= Delay () (n outLam)

    -- x is bound so it is left alone
    -- y is discharged from the env
    -- outOfScope is free so it is left alone
    -- dis( y:unit |- \x-> x y outOfScope) ) === (\x -> x unit outOfScope)
    dis (VLamAbs (fakeNameDeBruijn $ DeBruijn 0)
         (n
         (mkIterApp ()
           (Var () (DeBruijn 1))
           [Var () (DeBruijn 2)
           ,outOfScope
           ]
         )
         )
         (cons (VCon $ someValue ()) empty)
        )
        @?= n (mkLam $ mkIterApp ()
                          (Var () (DeBruijn 1))
                          [ Constant () (someValue ())
                          , outOfScope
                          ]
              )
 where
     dis = dischargeCekValue
     n = termMapNames fakeNameDeBruijn
