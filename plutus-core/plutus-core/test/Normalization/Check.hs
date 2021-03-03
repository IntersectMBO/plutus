{-# LANGUAGE OverloadedStrings #-}

module Normalization.Check ( test_normalizationCheck ) where

import           Language.PlutusCore
import           Language.PlutusCore.Check.Normal
import           Test.Tasty
import           Test.Tasty.HUnit

-- test that [rec (lam dat (fun (type) (type)) [dat a])] is a type value
test_applyToValue :: IO ()
test_applyToValue =
    let ty = TyApp ()
                recVar
                (TyLam () datName
                    (KindArrow () (Type ()) (Type ()))
                    (TyApp () datVar aVar)
                )
    in isNormalType ty @?= True

    where recVar = TyVar () (TyName (Name "rec" (Unique 0)))
          datVar = TyVar () datName
          datName = TyName (Name "dat" (Unique 1))
          aVar = TyVar () (TyName (Name "a" (Unique 2)))

test_normalizationCheck :: TestTree
test_normalizationCheck =
    testGroup "isTypeValue"
        [ testCase "valueApply" test_applyToValue ]
