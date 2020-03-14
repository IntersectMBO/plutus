{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}

module TypeSynthesis.Spec
    ( test_typecheck
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.FsTree              (foldPlcFolderContents)
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.Examples.Everything (examples)
import           Language.PlutusCore.StdLib.Everything   (stdLib)

import           Common

import           Control.Monad.Except
import           System.FilePath                         ((</>))
import           Test.Tasty
import           Test.Tasty.HUnit

kindcheck :: MonadError (Error uni ()) m => Type TyName uni () -> m (Type TyName uni ())
kindcheck ty = do
    _ <- runQuoteT $ inferKind defOffChainConfig ty
    return ty

typecheck :: (uni ~ DefaultUni, MonadError (Error uni ()) m) => Term TyName Name uni () -> m ()
typecheck term = do
    _ <- runQuoteT $ inferType defOffChainConfig term
    return ()

-- | Assert a 'Type' is well-kinded.
assertWellKinded :: HasCallStack => Type TyName DefaultUni () -> Assertion
assertWellKinded ty = case runExcept . runQuoteT $ kindcheck ty of
    Left  err -> assertFailure $ "Kind error: " ++ prettyPlcCondensedErrorClassicString err
    Right _   -> return ()

-- | Assert a 'Term' is well-typed.
assertWellTyped :: HasCallStack => Term TyName Name DefaultUni () -> Assertion
assertWellTyped term = case runExcept . runQuoteT $ typecheck term of
    Left  err -> assertFailure $ "Type error: " ++ prettyPlcCondensedErrorClassicString err
    Right _   -> return ()

-- | Assert a term is ill-typed.
assertIllTyped :: HasCallStack => Term TyName Name DefaultUni () -> Assertion
assertIllTyped term = case runExcept . runQuoteT $ typecheck term of
    Right () -> assertFailure $ "Well-typed: " ++ prettyPlcCondensedErrorClassicString term
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
selfApply :: Term TyName Name uni ()
selfApply = runQuote $ do
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
            [ selfApply
            ]

test_typecheckBuiltinName :: BuiltinName -> TestTree
test_typecheckBuiltinName name = goldenVsDoc testName path doc where
    testName = show name
    path     = "test" </> "TypeSynthesis" </> "Golden" </> (testName ++ ".plc.golden")
    doc      = prettyPlcDef $ typeOfBuiltinName @DefaultUni name

test_typecheckBuiltinNames :: TestTree
test_typecheckBuiltinNames =
    testGroup "built-in name" $ map test_typecheckBuiltinName allBuiltinNames

test_typecheck :: TestTree
test_typecheck =
    testGroup "typecheck"
        [ test_typecheckBuiltinNames
        , test_typecheckAvailable
        , test_typecheckIllTyped
        ]
