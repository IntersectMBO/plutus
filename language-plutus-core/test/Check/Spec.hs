{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Check.Spec (tests) where

import           Language.PlutusCore
import qualified Language.PlutusCore.Check.Uniques          as Uniques
import qualified Language.PlutusCore.Check.ValueRestriction as VR
import           Language.PlutusCore.Generators.AST
import           Language.PlutusCore.Quote
import           PlutusPrelude

import           Control.Monad.Except
import           Data.Foldable                              (traverse_)
import           Hedgehog                                   hiding (Var)
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "checks"
    [ testProperty "renaming ensures global uniqueness" propRenameCheck
    , shadowed
    , multiplyDefined
    , incoherentUse
    , valueRestriction
    ]

data Tag = Tag Int | Ignore deriving (Show, Eq, Ord)

checkTermUniques :: (Ord a, MonadError (UniqueError a) m) => Term TyName Name a -> m ()
checkTermUniques = Uniques.checkTerm (\case FreeVariable{} -> False; _ -> True)

shadowed :: TestTree
shadowed =
    let
        u = Unique (-1)
        checked = runExcept $ runQuoteT $ do
            ty <- freshTyName Ignore "ty"
            let n = Name Ignore "yo" u
            let term =
                    LamAbs (Tag 1) n (TyVar Ignore ty) $
                    LamAbs (Tag 2) n (TyVar Ignore ty) $
                    Var Ignore n
            checkTermUniques term
        assertion = checked @?= Left (MultiplyDefined u (Tag 1) (Tag 2))
    in testCase "shadowed" assertion

multiplyDefined :: TestTree
multiplyDefined =
    let
        u = Unique (-1)
        checked = runExcept $ runQuoteT $ do
            ty <- freshTyName Ignore "ty"
            let n = Name Ignore "yo" u
            let term =
                    Apply Ignore
                    (LamAbs (Tag 1) n (TyVar Ignore ty) (Var Ignore n))
                    (LamAbs (Tag 2) n (TyVar Ignore ty) (Var Ignore n))
            checkTermUniques term
        assertion = checked @?= Left (MultiplyDefined u (Tag 1) (Tag 2))
    in testCase "multiplyDefined" assertion

incoherentUse :: TestTree
incoherentUse =
    let
        u = Unique 0
        checked = runExcept $ runQuoteT $ do
            let n = Name Ignore "yo" u
            let ty = TyName n
            let term =
                    LamAbs (Tag 1) n (TyVar (Tag 2) ty) $
                    TyInst Ignore (Var (Tag 3) n) (TyVar (Tag 4) ty)
            checkTermUniques term
        assertion = checked @?= Left (IncoherentUsage u (Tag 1) (Tag 2))
    in testCase "incoherentUse" assertion

propRenameCheck :: Property
propRenameCheck = property $ do
    prog <- forAll genProgram
    -- we didn't generate prog in Quote, so mark all the uniques as non-fresh
    renamed <- runQuoteT $ (rename <=< through markNonFreshProgram) prog
    annotateShow renamed
    Hedgehog.evalExceptT $ checkUniques renamed
        where
            checkUniques :: (Ord a, MonadError (UniqueError a) m) => Program TyName Name a -> m ()
            -- the renamer will fix incoherency between *bound* variables, but it ignores free variables, so
            -- we can still get incoherent usage errors, ignore them for now
            checkUniques = Uniques.checkProgram (\case { FreeVariable{} -> False; IncoherentUsage {} -> False; _ -> True})

valueRestriction :: TestTree
valueRestriction =
    let terms = runQuote $ do
            aN <- freshTyName () "a"
            bN <- freshTyName () "b"
            x <- freshName () "x"
            let typeAbs v = TyAbs () v (Type ())
                aV = TyVar () aN
                xV = Var () x
            pure [ ( typeAbs aN $ Error () aV
                   , Left $ ValueRestrictionViolation () aN
                   )
                 , ( typeAbs aN . typeAbs bN $ Error () aV
                   , Left $ ValueRestrictionViolation () bN
                   )
                 , ( typeAbs aN $ LamAbs () x aV xV
                   , Right ()
                   )
                 , ( typeAbs aN . typeAbs bN $ LamAbs () x aV xV
                   , Right ()
                   )
                 ]
        assertion = traverse_ (\(term, res) -> VR.checkTerm term @?= res) terms
    in testCase "valueRestriction" assertion
