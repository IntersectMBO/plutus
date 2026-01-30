{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Evaluation.FreeVars (test_freevars) where

import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.MkPlc
import PlutusCore.StdLib.Data.Unit
import PlutusPrelude
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal
import UntypedPlutusCore.Test.DeBruijn.Bad
import UntypedPlutusCore.Test.DeBruijn.Good

import Test.Tasty
import Test.Tasty.HUnit

{-| Test the behaviour of Cek evaluator module *directly*
by using the Internal module, thus bypassing any prior term conformance checks, e.g.
that the term is closed (no free variables). -}
testCekInternalFree :: TestTree
testCekInternalFree =
  testGroup "cekInternal" $
    fmap
      (uncurry testCase)
      [ ("delay0", eval (Delay () var0) @?= True)
      , ("fun0var0", eval fun0var0 @?= True)
      , -- Interesting example because it is a `const x y` where x is a value and y is out-of-scope.
        -- The evaluation result (success or failure) depends on how the machine
        -- ignores  the irrelevant to the computation) part of the environment.
        ("const0var0", eval (const0 @@ [unitval, fun0var0]) @?= True)
      , -- same as above, plus match on discharged value to show that freevar is completely ignored
        ("const0var0Discharge", evalV (const0 @@ [unitval, fun0var0]) @?= Right unitval)
      , ("iteLazy0", eval iteLazy0 @?= True)
      , ("iteStrict0", eval iteStrict0 @?= False)
      , ("illITELazy", eval illITELazy @?= True)
      , ("illITEStrict", eval illITEStrict @?= True)
      , ("illAdd", eval illAdd @?= False)
      , ("illOverAppBuiltin", eval illOverAppBuiltin @?= False)
      , ("illOverAppFun", eval illOverAppFun @?= False)
      ]
  where
    evalV =
      toFakeTerm
        >>> runCekDeBruijn PLC.defaultCekParametersForTesting counting noEmitter
        >>> _cekReportResult
        >>> cekResultToEither

    eval =
      evalV
        >>> isRight

{-| Test the behaviour of discharge function against open terms (containing free variables)
by manually constructing CekValue's and Cek Environment's. The free variables should
be left untouched. -}
testDischargeFree :: TestTree
testDischargeFree =
  testGroup "discharge" $
    fmap
      (uncurry testCase)
      [ ("delayWithEmptyEnv", delayWithEmptyEnv)
      , ("boundEnvAndFreeVars", boundEnvAndFreeVars)
      , ("freeRemainsUnderLambda", freeRemainsUnderLambda)
      , ("freeRemainsUnder2Lambdas", freeRemainsUnder2Lambdas)
      , ("freeRemainsUnder3Lambdas", freeRemainsUnder3Lambdas)
      , ("freeRemainsInNestedEnv", freeRemainsInNestedEnv)
      , ("deepFreeVarRemains", deepFreeVarRemains)
      , ("multipleFreeVarsRemain", multipleFreeVarsRemain)
      ]
  where
    delayWithEmptyEnv =
      -- dis( empty |- (delay (\x ->var0)) ) === (delay (\x -> var0))
      dis
        ( VDelay
            (toFakeTerm fun0var0)
            [] -- empty env
        )
        @?= DischargeNonConstant (toFakeTerm $ Delay () fun0var0)

    boundEnvAndFreeVars =
      -- dis( y:unit |- \x-> x y var0) ) === (\x -> x unit var0)
      -- x is bound so it is left alone
      -- y is discharged from the env
      -- var0 is free so it is left alone
      dis
        ( VLamAbs
            (fakeNameDeBruijn $ DeBruijn deBruijnInitIndex)
            ( toFakeTerm $
                v 1
                  @@ [ v 2 -- x
                  -- y
                     , var0 -- free
                     ]
            )
            [VCon $ someValue ()] -- env has y
        )
        @?= DischargeNonConstant
          ( toFakeTerm . lamAbs0 $
              v 1
                @@ [ Constant () (someValue ()) -- x
                -- substituted y
                   , var0 -- free
                   ]
          )

    freeRemainsUnderLambda =
      -- Issue #7526: Variable capture in dischargeCekValue
      -- (\\0 \\0 var 2) (delay (var 1)) evaluates to:
      --   VLamAbs _ (var 2) [VDelay (var 1) []]
      -- Free var 1 in delay should shift to var 2 under 1 lambda
      dis
        ( VLamAbs
            (fakeNameDeBruijn $ DeBruijn deBruijnInitIndex)
            (toFakeTerm $ v 2)
            [VDelay (toFakeTerm $ v 1) []]
        )
        @?= DischargeNonConstant
          ( toFakeTerm . lamAbs0 $
              Delay () (v 2) -- var 1 shifted by 1
          )

    freeRemainsUnder2Lambdas =
      -- VLamAbs _ (LamAbs _ (var 3)) [VDelay (var 1) []]
      -- Body var 3 under 2 lambdas looks up idx 3-2=1 in env -> VDelay (var 1) []
      -- Free var 1 in delay should shift to var 3 under 2 lambdas
      dis
        ( VLamAbs
            (fakeNameDeBruijn $ DeBruijn deBruijnInitIndex)
            ( toFakeTerm $
                LamAbs () (DeBruijn deBruijnInitIndex) (v 3)
            )
            [VDelay (toFakeTerm $ v 1) []]
        )
        @?= DischargeNonConstant
          ( toFakeTerm . lamAbs0 . lamAbs0 $
              Delay () (v 3) -- var 1 shifted by 2
          )

    freeRemainsUnder3Lambdas =
      -- Same pattern but with 3 lambdas
      -- Free var 1 should shift to var 4 under 3 lambdas
      dis
        ( VLamAbs
            (fakeNameDeBruijn $ DeBruijn deBruijnInitIndex)
            ( toFakeTerm $
                LamAbs () (DeBruijn deBruijnInitIndex) $
                  LamAbs () (DeBruijn deBruijnInitIndex) (v 4)
            )
            [VDelay (toFakeTerm $ v 1) []]
        )
        @?= DischargeNonConstant
          ( toFakeTerm . lamAbs0 . lamAbs0 . lamAbs0 $
              Delay () (v 4) -- var 1 shifted by 3
          )

    freeRemainsInNestedEnv =
      -- Outer: VLamAbs _ (var 2) [innerVal]
      -- Inner: VLamAbs _ (var 2) [VDelay (var 1) []]
      -- Discharging: \\0 (\\0 delay (var ?))
      -- Free var 1 should shift to var 3 (1 from outer + 1 from inner lambda)
      dis
        ( VLamAbs
            (fakeNameDeBruijn $ DeBruijn deBruijnInitIndex)
            (toFakeTerm $ v 2)
            [ VLamAbs
                (fakeNameDeBruijn $ DeBruijn deBruijnInitIndex)
                (toFakeTerm $ v 2)
                [VDelay (toFakeTerm $ v 1) []]
            ]
        )
        @?= DischargeNonConstant
          ( toFakeTerm . lamAbs0 . lamAbs0 $
              Delay () (v 3) -- var 1 shifted by 2 (1 from each lambda)
          )

    deepFreeVarRemains =
      -- VLamAbs _ (var 2) [VDelay (var 3) []]
      -- var 3 in delay is free and deeply indexed
      -- Should shift to var 4 under 1 lambda
      dis
        ( VLamAbs
            (fakeNameDeBruijn $ DeBruijn deBruijnInitIndex)
            (toFakeTerm $ v 2)
            [VDelay (toFakeTerm $ v 3) []]
        )
        @?= DischargeNonConstant
          ( toFakeTerm . lamAbs0 $
              Delay () (v 4) -- var 3 shifted by 1
          )

    multipleFreeVarsRemain =
      -- VLamAbs _ (LamAbs _ (var 3)) [VDelay (var 1 @ var 2) []]
      -- var 1 and var 2 in delay are both free
      -- Both should shift by 2: var 1 -> var 3, var 2 -> var 4
      dis
        ( VLamAbs
            (fakeNameDeBruijn $ DeBruijn deBruijnInitIndex)
            ( toFakeTerm $
                LamAbs () (DeBruijn deBruijnInitIndex) (v 3)
            )
            [VDelay (toFakeTerm $ v 1 @@ [v 2]) []]
        )
        @?= DischargeNonConstant
          ( toFakeTerm . lamAbs0 . lamAbs0 $
              Delay () (v 3 @@ [v 4]) -- var 1 -> var 3, var 2 -> var 4
          )

    dis = dischargeCekValue @DefaultUni @DefaultFun
    v = Var () . DeBruijn

test_freevars :: TestTree
test_freevars =
  testGroup
    "FreeVars"
    [ testCekInternalFree
    , testDischargeFree
    ]

-- shortcuts
toFakeTerm :: Term DeBruijn uni fun ann -> Term NamedDeBruijn uni fun ann
toFakeTerm = termMapNames fakeNameDeBruijn
