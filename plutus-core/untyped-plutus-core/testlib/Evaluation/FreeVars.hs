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
      [ ("freeRemains1", freeRemains1)
      , ("freeRemains2", freeRemains2)
      ]
  where
    freeRemains1 =
      -- dis( empty |- (delay (\x ->var0)) ) === (delay (\x -> var0))
      dis
        ( VDelay
            (toFakeTerm fun0var0)
            [] -- empty env
        )
        @?= DischargeNonConstant (toFakeTerm $ Delay () fun0var0)

    freeRemains2 =
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
