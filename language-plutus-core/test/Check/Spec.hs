{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Check.Spec (tests) where

import           Language.PlutusCore
import qualified Language.PlutusCore.Check.Normal   as Normal
import qualified Language.PlutusCore.Check.Uniques  as Uniques
import qualified Language.PlutusCore.Check.Value    as VR
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Generators.AST

import           Control.Monad.Except
import           Data.Either
import           Hedgehog                           hiding (Var)
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "checks"
    [ testProperty "renaming ensures global uniqueness" propRenameCheck
    , shadowed
    , multiplyDefined
    , incoherentUse
    , values
    , valueRestriction
    , normalTypes
    , normalTypesCheck
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
    renamed <- runQuoteT $ rename prog
    annotateShow renamed
    Hedgehog.evalExceptT $ checkUniques renamed
        where
            checkUniques :: (Ord a, MonadError (UniqueError a) m) => Program TyName Name a -> m ()
            -- the renamer will fix incoherency between *bound* variables, but it ignores free variables, so
            -- we can still get incoherent usage errors, ignore them for now
            checkUniques = Uniques.checkProgram (\case { FreeVariable{} -> False; IncoherentUsage {} -> False; _ -> True})

valueRestriction :: TestTree
valueRestriction = runQuote $ do
    aN <- freshTyName () "a"
    bN <- freshTyName () "b"
    xN <- freshName () "x"
    let typeAbs v = TyAbs () v (Type ())
        aV = TyVar () aN
        xV = Var () xN
    pure $ testGroup "value restriction" [
        testCase "absError" $ isLeft (checkVR (typeAbs aN $ Error () aV)) @? "Value restriction"
      , testCase "nestedAbsError" $ isLeft (checkVR (typeAbs aN . typeAbs bN $ Error () aV)) @? "Value restriction"
      , testCase "wrapError" $ isLeft (checkVR (typeAbs aN $ IWrap () aV aV $ Error () aV)) @? "Value restriction"

      , testCase "absLam" $ isRight (checkVR (typeAbs aN $ LamAbs () xN aV xV)) @? "Value restriction"
      , testCase "nestedAbsLam" $ isRight (checkVR (typeAbs aN . typeAbs bN $ LamAbs () xN aV xV)) @? "Value restriction"
      ]
        where
            checkVR :: Term TyName Name () -> Either (VR.ValueRestrictionError TyName ()) ()
            checkVR = VR.checkTerm

values :: TestTree
values = runQuote $ do
    aN <- freshTyName () "a"
    let aV = TyVar () aN
        val = makeIntConstant 2
        nonVal = Error () aV
    pure $ testGroup "values" [
          testCase "wrapNonValue" $ VR.isTermValue (IWrap () aV aV nonVal) @?= False
        , testCase "wrapValue" $ VR.isTermValue (IWrap () aV aV val) @?= True

        , testCase "absNonValue" $ VR.isTermValue (TyAbs () aN (Type ()) nonVal) @?= False
        , testCase "absValue" $ VR.isTermValue (TyAbs () aN (Type()) val) @?= True

        , testCase "error" $ VR.isTermValue (Error () aV) @?= False
        , testCase "lam" $ VR.isTermValue (LamAbs () (Var () aN) aV nonVal) @?= True
        , testCase "app" $ VR.isTermValue (Apply () val val) @?= False
        , testCase "unwrap" $ VR.isTermValue (Unwrap () val) @?= False
        , testCase "inst" $ VR.isTermValue (TyInst () val aV) @?= False
        , testCase "constant" $ VR.isTermValue (makeIntConstant 1) @?= True
        , testCase "builtin" $ VR.isTermValue (builtinNameAsTerm AddInteger) @?= False
      ]

normalTypes :: TestTree
normalTypes = runQuote $ do
    aN <- freshTyName () "a"
    let integer = TyBuiltin () TyInteger
        aV = TyVar () aN
        neutral = integer
        normal = integer
        nonNormal = TyApp () (TyLam () aN (Type ()) aV) normal
    pure $ testGroup "normal types" [
          testCase "var" $ Normal.isNormalType aV @?= True

        , testCase "funNormal" $ Normal.isNormalType (TyFun () normal normal) @?= True
        , testCase "funNotNormal" $ Normal.isNormalType (TyFun () normal nonNormal) @?= False

        , testCase "lamNormal" $ Normal.isNormalType (TyLam () aN (Type ()) normal) @?= True
        , testCase "lamNonNormal" $ Normal.isNormalType (TyLam () aN (Type ()) nonNormal) @?= False

        , testCase "forallNormal" $ Normal.isNormalType (TyForall () aN (Type ()) normal) @?= True
        , testCase "forallNonNormal" $ Normal.isNormalType (TyForall () aN (Type ()) nonNormal) @?= False

        , testCase "ifixNormal" $ Normal.isNormalType (TyIFix () normal normal) @?= True
        , testCase "ifixNonNormal" $ Normal.isNormalType (TyIFix () nonNormal normal) @?= False

        , testCase "appNormal" $ Normal.isNormalType (TyApp () neutral normal) @?= True
        , testCase "appNonNormal" $ Normal.isNormalType (TyApp () nonNormal normal) @?= False

        , testCase "builtin" $ Normal.isNormalType integer @?= True
      ]

normalTypesCheck :: TestTree
normalTypesCheck = runQuote $ do
    aN <- freshTyName () "a"
    xN <- freshName () "x"
    let integer = TyBuiltin () TyInteger
        aV = TyVar () aN
        xV = Var () xN
        normal = integer
        nonNormal = TyApp () (TyLam () aN (Type ()) aV) normal
    pure $ testGroup "normalized types check" [
        testCase "lamNormal" $ isRight (checkNormal (LamAbs () xN normal xV)) @? "Normalization"
        , testCase "lamNonNormal" $ isLeft (checkNormal (LamAbs () xN nonNormal xV)) @? "Normalization"

        , testCase "abs" $ isRight (checkNormal (TyAbs () aN (Type ()) xV)) @? "Normalization"

        , testCase "wrapNormal" $ isRight (checkNormal (IWrap () normal normal xV)) @? "Normalization"
        , testCase "wrapNonNormal" $ isLeft (checkNormal (IWrap () nonNormal nonNormal xV)) @? "Normalization"

        , testCase "unwrap" $ isRight (checkNormal (Unwrap () xV)) @? "Normalization"

        , testCase "app" $ isRight (checkNormal (Apply () xV xV)) @? "Normalization"

        , testCase "errorNormal" $ isRight (checkNormal (Error () normal)) @? "Normalization"
        , testCase "errorNonNormal" $ isLeft (checkNormal (Error () nonNormal)) @? "Normalization"

        , testCase "constant" $ isRight (checkNormal (makeIntConstant 2)) @? "Normalization"
        , testCase "builtin" $ isRight (checkNormal (builtinNameAsTerm AddInteger)) @? "Normalization"
      ]
        where
            checkNormal :: Term TyName Name () -> Either (Normal.NormalizationError TyName Name ()) ()
            checkNormal = Normal.checkTerm
