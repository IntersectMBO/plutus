{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusIR.Contexts.Tests where

import PlutusIR
import PlutusIR.Contexts

import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Name.Unique (Unique (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

test_extractTyArgs :: TestTree
test_extractTyArgs =
  testGroup
    "Applying extractTyArgs to an"
    [ testCase "empty AppContext evaluates to an empty list of ty args" do
        extractTyArgs AppContextEnd @?= Just ([] :: [Type TyName DefaultUni ()])
    , testCase "AppContext without type applications evaluates to Nothing" do
        extractTyArgs (TermAppContext term () AppContextEnd) @?= Nothing
    , testCase "AppContext with a mix of term and type applications evaluates to Nothing" do
        extractTyArgs (TypeAppContext ty1 () (TermAppContext term () AppContextEnd)) @?= Nothing
        extractTyArgs (TermAppContext term () (TypeAppContext ty1 () AppContextEnd)) @?= Nothing
    , testCase "AppContext with type applications only evaluates to Just (list of ty vars)" do
        extractTyArgs (TypeAppContext ty1 () (TypeAppContext ty2 () AppContextEnd))
          @?= Just [ty1, ty2]
    ]

----------------------------------------------------------------------------------------------------
-- Test values -------------------------------------------------------------------------------------

term :: Term TyName Name DefaultUni DefaultFun ()
term = Var () (Name "x" (Unique 0))

ty1 :: Type TyName DefaultUni ()
ty1 = TyVar () (TyName (Name "t" (Unique 0)))

ty2 :: Type TyName DefaultUni ()
ty2 = TyVar () (TyName (Name "t" (Unique 1)))
