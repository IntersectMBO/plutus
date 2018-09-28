{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Evaluation.TypeCheck
    ( test_typecheck
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.ChurchNat
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit

import           Control.Monad.Except

import           Test.Tasty
import           Test.Tasty.HUnit

-- | Assert a 'Term' is well-typed.
assertQuoteWellTyped :: HasCallStack => Quote (Term TyName Name ()) -> Assertion
assertQuoteWellTyped getTerm = case runExcept . runQuoteT $ typecheck getTerm of
    Left  err -> assertFailure $ " Type error: " ++ prettyPlcDefString err
    Right _   -> return ()

-- | Assert a term is ill-typed.
assertQuoteIllTyped :: HasCallStack => Quote (Term TyName Name ()) -> Assertion
assertQuoteIllTyped getTerm = case runExcept . runQuoteT $ typecheck getTerm of
    Right term -> assertFailure $ "Well-typed: " ++ prettyPlcDefString term
    Left  _    -> return ()

typecheck
    :: (MonadError (Error ()) m, MonadQuote m)
    => Quote (Term TyName Name ()) -> m (Term TyName Name ())
typecheck getTerm = do
    term <- liftQuote getTerm
    annotated <- annotateTerm term
    _ <- typecheckTerm 1000 annotated
    return term

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

test_typecheckPrelude :: TestTree
test_typecheckPrelude = testCase "Prelude" $ foldMap assertQuoteWellTyped
    [ getBuiltinConst
    , getBuiltinUnitval
    , getBuiltinTrue
    , getBuiltinFalse
    , getBuiltinIf
    ]

test_typecheckTerms :: TestTree
test_typecheckTerms = testCase "terms" $ foldMap assertQuoteWellTyped
    [ getBuiltinUnroll
    , getBuiltinFix
    , getBuiltinFixN 2
    , getBuiltinChurchZero
    , getBuiltinChurchSucc
    , getBuiltinZero
    , getBuiltinSucc
    , getBuiltinFoldrNat
    , getBuiltinFoldNat
    , getBuiltinNil
    , getBuiltinCons
    , getBuiltinFoldrList
    , getBuiltinFoldList
    , getBuiltinSum 1
    ]

test_typecheckIllTyped :: TestTree
test_typecheckIllTyped = testCase "ill-typed" $ foldMap assertQuoteIllTyped
    [ getBuiltinSelfApply
    ]

test_typecheck :: TestTree
test_typecheck = testGroup "typecheck"
    [ test_typecheckPrelude
    , test_typecheckTerms
    , test_typecheckIllTyped
    ]
