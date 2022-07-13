{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module TypeSynthesis.Spec
    ( test_typecheck
    ) where

import PlutusPrelude

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Error
import PlutusCore.FsTree
import PlutusCore.MkPlc
import PlutusCore.Pretty

import PlutusCore.Examples.Builtins
import PlutusCore.Examples.Everything (builtins, examples)
import PlutusCore.StdLib.Everything (stdLib)

import Control.Monad.Except
import System.FilePath ((</>))
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.HUnit

kindcheck
    :: (uni ~ DefaultUni, fun ~ DefaultFun, MonadError (Error uni fun ()) m)
    => Type TyName uni () -> m (Type TyName uni ())
kindcheck ty = do
    _ <- runQuoteT $ inferKind defKindCheckConfig ty
    return ty

typecheck
    :: (uni ~ DefaultUni, MonadError (Error uni fun ()) m, ToBuiltinMeaning uni fun)
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
assertWellTyped
    :: (HasCallStack, ToBuiltinMeaning DefaultUni fun, Pretty fun)
    => Term TyName Name DefaultUni fun () -> Assertion
assertWellTyped term = case runExcept . runQuoteT $ typecheck term of
    Left  err -> assertFailure $ "Type error: " ++ displayPlcCondensedErrorClassic err
    Right _   -> return ()

-- | Assert a term is ill-typed.
assertIllTyped
    :: HasCallStack
    => Term TyName Name DefaultUni DefaultFun ()
    -> (Error DefaultUni DefaultFun () -> Bool)
    -> Assertion
assertIllTyped term isExpected = case runExcept . runQuoteT $ typecheck term of
    Right () -> assertFailure $ "Well-typed: " ++ displayPlcCondensedErrorClassic term
    Left err -> do
        unless (isExpected err) $
            assertFailure $ "Got an unexpected error: " ++ displayPlcCondensedErrorClassic err

foldAssertWell
    :: (ToBuiltinMeaning DefaultUni fun, Pretty fun)
    => PlcFolderContents DefaultUni fun -> [TestTree]
foldAssertWell =
    foldPlcFolderContents
        testGroup
        (\name -> testCase name . assertWellKinded)
        (\name -> testCase name . assertWellTyped)

test_typecheckAvailable :: TestTree
test_typecheckAvailable =
    testGroup "Available"
        [ testGroup "DefaultFun"   $ foldAssertWell stdLib
        , testGroup "ExtensionFun" $ foldAssertWell builtins
        , testGroup "Both"         $ foldAssertWell examples
        ]

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

-- | For checking that attempting to reference a type variable whose name got shadowed results in a
-- type error.
mismatchTyName :: Term TyName Name uni fun ()
mismatchTyName =
    let toTyName txt = TyName (Name txt (Unique 0)) in
        Error ()
      . TyLam () (toTyName "x") (Type ())
      . TyLam () (toTyName "y") (Type ())
      $ TyVar () (toTyName "x")

-- | For checking that attempting to reference a variable whose name got shadowed results in a
-- type error.
mismatchName :: Term TyName Name DefaultUni fun ()
mismatchName =
    let toName txt = Name txt (Unique 0) in
        LamAbs () (toName "x") (mkTyBuiltin @_ @Integer ())
      . LamAbs () (toName "y") (mkTyBuiltin @_ @Integer ())
      $ Var () (toName "x")

test_typecheckIllTyped :: TestTree
test_typecheckIllTyped =
    testCase "ill-typed" $
        foldMap (uncurry assertIllTyped)
            [ (,) selfApply $ \case
                TypeErrorE (TypeMismatch {}) -> True
                _                            -> False
            , (,) mismatchTyName $ \case
                TypeErrorE (TyNameMismatch {}) -> True
                _                              -> False
            , (,) mismatchName $ \case
                TypeErrorE (NameMismatch {}) -> True
                _                            -> False
            ]

test_typecheckFun :: (ToBuiltinMeaning DefaultUni fun, Show fun) => fun -> TestTree
test_typecheckFun name = goldenVsDoc testName path doc where
    testName = show name
    path     = "plutus-core" </> "test" </> "TypeSynthesis" </> "Golden" </> (testName ++ ".plc.golden")
    doc      = prettyPlcDef $ typeOfBuiltinFunction @DefaultUni name

test_typecheckAllFun
    :: forall fun. (ToBuiltinMeaning DefaultUni fun, Show fun)
    => String -> TestTree
test_typecheckAllFun name = testGroup name . map test_typecheckFun $ enumerate @fun

test_typecheckDefaultFuns :: TestTree
test_typecheckDefaultFuns =
    testGroup "builtins"
        [ test_typecheckAllFun @DefaultFun "DefaultFun"
        , test_typecheckAllFun @ExtensionFun "ExtensionFun"
        ]

test_typecheck :: TestTree
test_typecheck =
    testGroup "typecheck"
        [ test_typecheckDefaultFuns
        , test_typecheckAvailable
        , test_typecheckIllTyped
        ]
