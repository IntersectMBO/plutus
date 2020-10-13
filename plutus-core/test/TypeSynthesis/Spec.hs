{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}

module TypeSynthesis.Spec
    ( test_typecheck
    ) where

import           PlutusPrelude

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.FsTree              (foldPlcFolderContents)
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.Examples.Everything (examples)
import           Language.PlutusCore.StdLib.Everything   (stdLib)

import           Common

import           Control.Monad.Except
import           System.FilePath                         ((</>))
import           Test.Tasty
import           Test.Tasty.HUnit

kindcheck
    :: (uni ~ DefaultUni, fun ~ DefaultFun, MonadError (Error uni fun ()) m)
    => Type TyName uni () -> m (Type TyName uni ())
kindcheck ty = do
    _ <- runQuoteT $ do
        tcConfig <- getDefTypeCheckConfig ()
        inferKind tcConfig ty
    return ty

typecheck
    :: (uni ~ DefaultUni, fun ~ DefaultFun, MonadError (Error uni fun ()) m)
    => Term TyName Name uni fun () -> m ()
typecheck term = do
    _ <- runQuoteT $ do
        tcConfig <- getDefTypeCheckConfig ()
        inferType tcConfig term
    return ()

-- | Assert a 'Type' is well-kinded.
assertWellKinded :: HasCallStack => Type TyName DefaultUni () -> Assertion
assertWellKinded ty = case runExcept . runQuoteT $ kindcheck ty of
    Left  err -> assertFailure $ "Kind error: " ++ displayPlcCondensedErrorClassic err
    Right _   -> return ()

-- | Assert a 'Term' is well-typed.
assertWellTyped :: HasCallStack => Term TyName Name DefaultUni DefaultFun () -> Assertion
assertWellTyped term = case runExcept . runQuoteT $ typecheck term of
    Left  err -> assertFailure $ "Type error: " ++ displayPlcCondensedErrorClassic err
    Right _   -> return ()

-- | Assert a term is ill-typed.
assertIllTyped :: HasCallStack => Term TyName Name DefaultUni DefaultFun () -> Assertion
assertIllTyped term = case runExcept . runQuoteT $ typecheck term of
    Right () -> assertFailure $ "Well-typed: " ++ displayPlcCondensedErrorClassic term
    Left  _  -> return ()

test_typecheckAvailable :: TestTree
test_typecheckAvailable =
    testGroup "Available" $
        foldPlcFolderContents
            testGroup
            (\name -> testCase name . assertWellKinded)
            (\name -> testCase name . assertWellTyped)
            (stdLib <> examples)

-- | Self-application. An example of ill-typed term.
--
-- > /\ (A :: *) -> \(x : A) -> x x
selfApply :: Term TyName Name uni fun ()
selfApply = runQuote $ do
    a <- freshTyName "a"
    x <- freshName "x"
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        . Apply () (Var () x)
        $ Var () x

test_typecheckIllTyped :: TestTree
test_typecheckIllTyped =
    testCase "ill-typed" $
        foldMap assertIllTyped
            [ selfApply
            ]

test_typecheckDefaultFun :: DefaultFun -> TestTree
test_typecheckDefaultFun name = goldenVsDoc testName path doc where
    testName = show name
    path     = "test" </> "TypeSynthesis" </> "Golden" </> (testName ++ ".plc.golden")
    doc      = prettyPlcDef $ typeOfBuiltinFunction @DefaultUni name

test_typecheckDefaultFuns :: TestTree
test_typecheckDefaultFuns =
    testGroup "built-in name" $ map test_typecheckDefaultFun enumeration

test_typecheck :: TestTree
test_typecheck =
    testGroup "typecheck"
        [ test_typecheckDefaultFuns
        , test_typecheckAvailable
        , test_typecheckIllTyped
        ]
