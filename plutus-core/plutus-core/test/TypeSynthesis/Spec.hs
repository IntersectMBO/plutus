-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module TypeSynthesis.Spec
  ( test_typecheck
  , lookupLastLessThanOrEqualTo
  ) where

import PlutusPrelude

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.FsTree
import PlutusCore.Pretty

import PlutusCore.Examples.Builtins
import PlutusCore.Examples.Everything (examples)
import PlutusCore.StdLib.Everything (stdLib)

import Control.Monad (unless)
import Control.Monad.Except
import Data.Text qualified as Text
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.HUnit

kindcheck
  :: (uni ~ DefaultUni, fun ~ DefaultFun, MonadError (Error uni fun ()) m)
  => Type TyName uni () -> m (Type TyName uni ())
kindcheck ty = do
  _ <- runQuoteT $ modifyError TypeErrorE $ inferKind defKindCheckConfig ty
  return ty

typecheck
  :: (uni ~ DefaultUni, MonadError (Error uni fun ()) m, ToBuiltinMeaning uni fun)
  => BuiltinSemanticsVariant fun
  -> Term TyName Name uni fun ()
  -> m (Normalized (Type TyName uni ()))
typecheck semvar term = runQuoteT $ modifyError TypeErrorE $ do
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
  Right _ -> assertFailure $ "Expected ill-typed but got well-typed: " ++ display term
  Left err -> do
    unless (isExpected err) $
      assertFailure $
        "Got an unexpected error: " ++ displayPlcCondensedErrorClassic err

nestedGoldenVsErrorOrThing :: (PrettyPlc e, PrettyReadable a) => String -> Either e a -> TestNested
nestedGoldenVsErrorOrThing name =
  nestedGoldenVsText name ".plc"
    . either displayPlcCondensedErrorClassic (render . prettyPlcReadableSimple . AsReadable)

foldAssertWell
  :: (ToBuiltinMeaning DefaultUni fun, Pretty fun)
  => BuiltinSemanticsVariant fun
  -> PlcFolderContents DefaultUni fun
  -> TestTree
foldAssertWell semvar =
  runTestNested ["plutus-core", "test", "TypeSynthesis", "Golden"]
    . foldPlcFolderContents
      testNested
      (\name -> nestedGoldenVsErrorOrThing name . kindcheck)
      (\name -> nestedGoldenVsErrorOrThing name . typecheck semvar)

test_typecheckAvailable :: TestTree
test_typecheckAvailable =
  let builtinSemanticsVariant :: ToBuiltinMeaning DefaultUni fun => BuiltinSemanticsVariant fun
      builtinSemanticsVariant = def
   in testGroup
        "Available"
        [ foldAssertWell builtinSemanticsVariant stdLib
        , foldAssertWell builtinSemanticsVariant examples
        ]

{-| Self-application. An example of ill-typed term.

> /\ (A :: *) -> \(x : A) -> x x -}
selfApply :: Term TyName Name uni fun ()
selfApply = runQuote $ do
  a <- freshTyName "a"
  x <- freshName "x"
  return
    . TyAbs () a (Type ())
    . LamAbs () x (TyVar () a)
    . Apply () (Var () x)
    $ Var () x

{-| For checking that attempting to reference a type variable whose name got shadowed results in a
type error. -}
mismatchTyName :: Term TyName Name uni fun ()
mismatchTyName =
  let toTyName txt = TyName (Name txt (Unique 0))
   in Error ()
        . TyLam () (toTyName "x") (Type ())
        . TyLam () (toTyName "y") (Type ())
        $ TyVar () (toTyName "x")

{-| For checking that attempting to reference a variable whose name got shadowed results in a
type error. -}
mismatchName :: Term TyName Name DefaultUni fun ()
mismatchName =
  let toName txt = Name txt (Unique 0)
   in LamAbs () (toName "x") (mkTyBuiltin @_ @Integer ())
        . LamAbs () (toName "y") (mkTyBuiltin @_ @Integer ())
        $ Var () (toName "x")

test_typecheckIllTyped :: TestTree
test_typecheckIllTyped =
  testCase "ill-typed" $
    foldMap
      (uncurry $ assertIllTyped def)
      [ (,) selfApply $ \case
          TypeErrorE (TypeMismatch {}) -> True
          _ -> False
      , (,) mismatchTyName $ \case
          TypeErrorE (TyNameMismatch {}) -> True
          _ -> False
      , (,) mismatchName $ \case
          TypeErrorE (NameMismatch {}) -> True
          _ -> False
      ]

test_typecheckAllFun
  :: forall fun
   . (ToBuiltinMeaning DefaultUni fun, Show fun, Show (BuiltinSemanticsVariant fun))
  => String
  -> BuiltinSemanticsVariant fun
  -> TestNested
test_typecheckAllFun name semVar =
  testNestedNamed name (show semVar)
    . map testFun
    $ enumerate @fun
  where
    testFun fun =
      nestedGoldenVsErrorOrThing (show fun) . kindcheck $ typeOfBuiltinFunction semVar fun

test_typecheckDefaultFuns :: TestTree
test_typecheckDefaultFuns =
  -- This checks that for each set of builtins the Plutus type of every builtin is the same
  -- regardless of versioning.
  testGroup "builtins" . pure $
    runTestNested ["plutus-core", "test", "TypeSynthesis", "Golden"] $
      concat
        [ map (test_typecheckAllFun @DefaultFun "DefaultFun") enumerate
        , map (test_typecheckAllFun @ExtensionFun "ExtensionFun") enumerate
        ]

{-| A value type to use in instantiated built-in signatures. We could use 'Term' or 'CekValue',
but those have type parameters and look unwieldy in type signatures, so we define a dedicated
value type to make golden tests more concise. -}
data Val = Val

type instance UniOf Val = DefaultUni
instance ExMemoryUsage Val where
  memoryUsage = error "Not supposed to be executed"
instance HasConstant Val where
  asConstant _ = throwError notAConstant
  fromConstant _ = Val

{-| Return the last element of the list that is smaller than or equal to the given one.

>>> let xs = [0, 2 .. 8 :: Int]
>>> lookupLastLessThanOrEqualTo (-1) xs
Nothing
>>> lookupLastLessThanOrEqualTo 0 xs
Just 0
>>> lookupLastLessThanOrEqualTo 3 xs
Just 2
>>> lookupLastLessThanOrEqualTo 11 xs
Just 8 -}
lookupLastLessThanOrEqualTo :: Ord a => a -> [a] -> Maybe a
lookupLastLessThanOrEqualTo _ [] = Nothing
lookupLastLessThanOrEqualTo xI (x0 : xs0)
  | xI < x0 = Nothing
  | otherwise = Just $ go x0 xs0
  where
    go x [] = x
    go x (x' : xs)
      | xI < x' = x
      | otherwise = go x' xs

{-| Dump the type signature of the denotation of each of the built-in functions to a golden file.
If the signature of the denotation of a built-in function has ever changed and that is reflected
in the semantics variants, then the signatures are dumped to @n + 1@ files where @n@ is the
number of changes (e.g. if there was only one, there'll be two golden files: the one for the
original signature and the other for the updated one). The number of semantics variants doesn't
matter, only the number of type signature changes (controlled by the second argument).

This design ensures that all type signature changes of denotations are explicitly reflected and
the addition of another semantics variant won't mask an unexpected change in the signature of a
denotation. -}
test_dumpTypeRepAllFun
  :: forall fun
   . ( ToBuiltinMeaning DefaultUni fun
     , Show fun
     , Show (BuiltinSemanticsVariant fun)
     , Ord (BuiltinSemanticsVariant fun)
     , Bounded (BuiltinSemanticsVariant fun)
     )
  => String
  -> [(fun, [BuiltinSemanticsVariant fun])]
  -> BuiltinSemanticsVariant fun
  -> TestNested
test_dumpTypeRepAllFun nameSet semVarChanges semVar =
  testNestedNamed nameSet (show semVar)
    . map testFun
    $ enumerate @fun
  where
    testFun fun =
      withTypeSchemeOfBuiltinFunction @Val semVar fun $ \sch -> do
        let name =
              show fun
                ++ case lookup fun semVarChanges of
                  Nothing -> ""
                  Just semVars -> ('_' :) . show $
                    case lookupLastLessThanOrEqualTo semVar semVars of
                      Nothing -> minBound
                      Just semVarLatest -> semVarLatest
        nestedGoldenVsText name ".sig" . Text.pack $ show sch

test_dumpTypeRepDefaultFuns :: TestTree
test_dumpTypeRepDefaultFuns =
  testGroup "builtin signatures" . pure $
    runTestNested ["plutus-core", "test", "TypeSynthesis", "Golden", "Signatures"] $
      concat
        [ let semVarChanges =
                -- Keep the inner lists sorted.
                [
                  ( ConsByteString
                  ,
                    [ DefaultFunSemanticsVariantC
                    ]
                  )
                ]
           in map (test_dumpTypeRepAllFun @DefaultFun "DefaultFun" semVarChanges) enumerate
        , let semVarChanges =
                -- Keep the inner lists sorted.
                [
                  ( IntNoIntegerNoWord
                  ,
                    [ ExtensionFunSemanticsVariant1
                    , ExtensionFunSemanticsVariant3
                    ]
                  )
                ]
           in map (test_dumpTypeRepAllFun @ExtensionFun "ExtensionFun" semVarChanges) enumerate
        ]

test_typecheck :: TestTree
test_typecheck =
  testGroup
    "typecheck"
    [ test_typecheckDefaultFuns
    , test_dumpTypeRepDefaultFuns
    , test_typecheckAvailable
    , test_typecheckIllTyped
    ]
