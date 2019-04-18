{-# LANGUAGE OverloadedStrings #-}

module ValueRestriction ( test_valueRestriction ) where

import Test.Tasty
import Language.PlutusCore
import Test.Tasty.HUnit

-- test that [rec (lam dat (fun (type) (type)) [dat a])] is a type value
test_valueApply :: IO ()
test_valueApply =
    let ty = TyApp ()
                recVar
                (TyLam () datName
                    (KindArrow () (Type ()) (Type ()))
                    (TyApp () datVar aVar)
                )
    in isTypeValue ty @?= True

    where recVar = TyVar () (TyName (Name () "rec" (Unique 0)))
          datVar = TyVar () datName
          datName = TyName (Name () "dat" (Unique 1))
          aVar = TyVar () (TyName (Name () "a" (Unique 2)))

test_valueRestriction :: TestTree
test_valueRestriction =
    testGroup "isTypeValue"
        [ testCase "valueApply" test_valueApply ]
