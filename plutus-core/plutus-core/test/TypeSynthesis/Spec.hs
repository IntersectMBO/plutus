-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module TypeSynthesis.Spec
    ( test_typecheck
    ) where

import PlutusPrelude

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Error
import PlutusCore.FsTree
import PlutusCore.Pretty

import PlutusCore.Examples.Builtins
import PlutusCore.Examples.Everything (examples)
import PlutusCore.StdLib.Everything (stdLib)

import Control.Monad (unless)
import Control.Monad.Except (MonadError, runExcept)
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
    => BuiltinSemanticsVariant fun
    -> Term TyName Name uni fun ()
    -> m (Normalized (Type TyName uni ()))
typecheck semvar term = runQuoteT $ do
    tcConfig <- TypeCheckConfig defKindCheckConfig <$> builtinMeaningsToTypes semvar ()
    inferType tcConfig term

-- | Assert a term is ill-typed.
assertIllTyped
    :: HasCallStack
    => BuiltinSemanticsVariant DefaultFun
    -> Term TyName Name DefaultUni DefaultFun ()
    -> (Error DefaultUni DefaultFun () -> Bool)
    -> Assertion
assertIllTyped semvar term isExpected = case runExcept . runQuoteT $ typecheck semvar term of
    Right _  -> assertFailure $ "Expected ill-typed but got well-typed: " ++ display term
    Left err -> do
        unless (isExpected err) $
            assertFailure $ "Got an unexpected error: " ++ displayPlcCondensedErrorClassic err

nestedGoldenVsErrorOrThing :: (PrettyPlc e, PrettyReadable a) => String -> Either e a -> TestNested
nestedGoldenVsErrorOrThing name =
    nestedGoldenVsText name ".plc" . either displayPlcCondensedErrorClassic (display . AsReadable)

foldAssertWell
    :: (ToBuiltinMeaning DefaultUni fun, Pretty fun)
    => BuiltinSemanticsVariant fun
    -> PlcFolderContents DefaultUni fun
    -> TestTree
foldAssertWell semvar
    = runTestNestedIn ["plutus-core", "test", "TypeSynthesis"]
    . testNested "Golden"
    . foldPlcFolderContents testNested
        (\name -> nestedGoldenVsErrorOrThing name . kindcheck)
        (\name -> nestedGoldenVsErrorOrThing name . typecheck semvar)

test_typecheckAvailable :: TestTree
test_typecheckAvailable =
    testGroup "Available"
        [ foldAssertWell def stdLib
        , foldAssertWell def examples
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
        foldMap (uncurry $ assertIllTyped def)
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

test_typecheckAllFun
    :: forall fun. (ToBuiltinMeaning DefaultUni fun, Show fun)
    => String
    -> BuiltinSemanticsVariant fun
    -> TestTree
test_typecheckAllFun name semvar
    = runTestNestedIn ["plutus-core", "test", "TypeSynthesis", "Golden"]
    . testNested name
    . map testFun
    $ enumerate @fun
  where
    testFun fun =
        nestedGoldenVsErrorOrThing (show fun) . kindcheck $ typeOfBuiltinFunction semvar fun

test_typecheckDefaultFuns :: TestTree
test_typecheckDefaultFuns =
    -- This checks that for each set of builtins the Plutus type of every builtin is the same
    -- regardless of versioning.
    testGroup "builtins" $ concat
        [ map (test_typecheckAllFun @DefaultFun "DefaultFun") enumerate
        , map (test_typecheckAllFun @ExtensionFun "ExtensionFun") enumerate
        ]

test_typecheck :: TestTree
test_typecheck =
    testGroup "typecheck"
        [ test_typecheckDefaultFuns
        , test_typecheckAvailable
        , test_typecheckIllTyped
        ]
