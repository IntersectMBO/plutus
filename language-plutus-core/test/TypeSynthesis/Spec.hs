{-# LANGUAGE OverloadedStrings #-}

module TypeSynthesis.Spec
    ( test_typecheck
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant          (typeOfBuiltinName)
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Everything

import           Common

import           Control.Monad.Except
import           System.FilePath                       ((</>))
import           Test.Tasty
import           Test.Tasty.HUnit

kindcheckQuoted
    :: (MonadError (Error ()) m, MonadQuote m)
    => Quote (Type TyName ()) -> m (Type TyName ())
kindcheckQuoted getType = do
    ty <- liftQuote getType
    _ <- annotateType ty >>= kindCheck (TypeConfig True mempty Nothing)
    return ty

typecheckQuoted
    :: (MonadError (Error ()) m, MonadQuote m)
    => Quote (Term TyName Name ()) -> m (Term TyName Name ())
typecheckQuoted getTerm = do
    term <- liftQuote getTerm
    _ <- annotateTerm term >>= typecheckTerm (TypeConfig True mempty (Just 1000))
    return term

-- | Assert a 'Type' is well-kinded.
assertWellKinded :: HasCallStack => Quote (Type TyName ()) -> Assertion
assertWellKinded getTy = case runExcept . runQuoteT $ kindcheckQuoted getTy of
    Left  err -> assertFailure $ "Kind error: " ++ prettyPlcCondensedErrorClassicString err
    Right _   -> return ()

-- | Assert a 'Term' is well-typed.
assertWellTyped :: HasCallStack => Quote (Term TyName Name ()) -> Assertion
assertWellTyped getTerm = case runExcept . runQuoteT $ typecheckQuoted getTerm of
    Left  err -> assertFailure $ "Type error: " ++ prettyPlcCondensedErrorClassicString err
    Right _   -> return ()

-- | Assert a term is ill-typed.
assertIllTyped :: HasCallStack => Quote (Term TyName Name ()) -> Assertion
assertIllTyped getTerm = case runExcept . runQuoteT $ typecheckQuoted getTerm of
    Right term -> assertFailure $ "Well-typed: " ++ prettyPlcCondensedErrorClassicString term
    Left  _    -> return ()

test_typecheckStdLib :: TestTree
test_typecheckStdLib =
    foldStdLib
        testGroup
        (\name -> testCase name . assertWellKinded)
        (\name -> testCase name . assertWellTyped)

-- | Self-application. An example of ill-typed term.
--
-- > /\ (A :: *) -> \(x : A) -> x x
getBuiltinSelfApply :: Quote (Term TyName Name ())
getBuiltinSelfApply = do
    a <- freshTyName () "a"
    x <- freshName () "x"
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        . Apply () (Var () x)
        $ Var () x

test_typecheckIllTyped :: TestTree
test_typecheckIllTyped =
    testCase "ill-typed" $
        foldMap assertIllTyped
            [ getBuiltinSelfApply
            ]

test_typecheckBuiltinName :: BuiltinName -> TestTree
test_typecheckBuiltinName name = goldenVsDoc testName path doc where
    testName = show name
    path     = "test" </> "TypeSynthesis" </> "Golden" </> (testName ++ ".plc.golden")
    doc      = prettyPlcDef . runQuote $ typeOfBuiltinName name

test_typecheckBuiltinNames :: TestTree
test_typecheckBuiltinNames =
    testGroup "built-in name" $ map test_typecheckBuiltinName allBuiltinNames

test_typecheck :: TestTree
test_typecheck =
    testGroup "typecheck"
        [ test_typecheckBuiltinNames
        , test_typecheckStdLib
        , test_typecheckIllTyped
        ]
