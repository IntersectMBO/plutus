{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

{-| This module contains tests that ensure the definition analysis is correct. We may consider
renaming this module, along with the corresponding PLC module to better reflect the scope. -}
module PlutusIR.Check.Uniques.Tests where

import Control.Monad.Except (MonadError, runExcept)
import Data.List.NonEmpty qualified as NE
import PlutusCore.Default (DefaultUni)
import PlutusCore.Error (UniqueError (..))
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.Name.Unique (Unique (..))
import PlutusCore.Quote (freshTyName, runQuoteT)
import PlutusIR.Check.Uniques qualified as Uniques
import PlutusIR.Core.Type
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (testCase, (@?=))

data Tag = Tag Int | Ignore deriving stock (Show, Eq, Ord)

checkTermUniques :: (Ord a, MonadError (UniqueError a) m) => Term TyName Name uni fun a -> m ()
checkTermUniques = Uniques.checkTerm (\case MultiplyDefined {} -> True; _ -> False)

test_shadowed :: TestTree
test_shadowed =
  let
    u = Unique (-1)
    checked = runExcept $ runQuoteT $ do
      ty <- freshTyName "ty"
      let n = Name "yo" u
      let term =
            LamAbs (Tag 1) n (TyVar Ignore ty) $
              LamAbs (Tag 2) n (TyVar Ignore ty) $
                Var Ignore n
      checkTermUniques term
    assertion = checked @?= Left (MultiplyDefined u (Tag 1) (Tag 2))
   in
    testCase "shadowed" assertion

test_multiplyDefined :: TestTree
test_multiplyDefined =
  let
    u = Unique (-1)
    checked = runExcept $ runQuoteT $ do
      ty <- freshTyName "ty"
      let n = Name "yo" u
      let term =
            Apply
              Ignore
              (LamAbs (Tag 1) n (TyVar Ignore ty) (Var Ignore n))
              (LamAbs (Tag 2) n (TyVar Ignore ty) (Var Ignore n))
      checkTermUniques term
    assertion = checked @?= Left (MultiplyDefined u (Tag 1) (Tag 2))
   in
    testCase "multiplyDefined" assertion

test_shadowedInLet :: TestTree
test_shadowedInLet =
  let
    u = Unique (-1)
    checked = runExcept $ runQuoteT $ do
      ty <- freshTyName "ty"
      let n = Name "yo" u
      let term =
            -- let n = 2 in \n -> n
            Let
              (Tag 1)
              NonRec
              ( NE.fromList
                  [ TermBind
                      (Tag 2)
                      Strict
                      ( VarDecl
                          { _varDeclAnn = Tag 3
                          , _varDeclName = n
                          , _varDeclType = TyVar Ignore ty
                          }
                      )
                      (mkConstant @Integer @DefaultUni (Tag 5) 2)
                  ]
              )
              ( LamAbs (Tag 4) n (TyVar Ignore ty) $
                  Var Ignore n
              )
      checkTermUniques term
    assertion = checked @?= Left (MultiplyDefined (Unique {unUnique = -1}) (Tag 3) (Tag 4))
   in
    testCase "shadowedInLet" assertion
