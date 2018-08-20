{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Evaluation.TypeCheck where

import           PlutusPrelude
import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Evaluation.Terms

import           Data.Foldable
import qualified Data.Text.Encoding as Text
import qualified Data.ByteString.Lazy as Bsl
import           Test.Tasty
import           Test.Tasty.HUnit

test_typecheckPrelude :: TestTree
test_typecheckPrelude = testCase "typecheckPrelude" $ foldMap assertFreshWellTyped
    [ getBuiltinConst
    , getBuiltinUnitval
    , getBuiltinTrue
    , getBuiltinFalse
    , getBuiltinIf
    ]

test_typecheckTerms :: TestTree
test_typecheckTerms = testCase "typecheckTerms" $ foldMap assertFreshWellTyped
    [ getBuiltinUnroll
    , getBuiltinFix
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
test_typecheckIllTyped = testCase "typecheckIllTyped" $ foldMap assertFreshIllTyped
    [ getBuiltinSelfApply
    ]

assertFreshWellTyped :: HasCallStack => Fresh (Term TyName Name ()) -> Assertion
assertFreshWellTyped getTerm =
    let term = unsafeRunFresh getTerm in
        for_ (typecheckTerm term) $ \err -> assertFailure $ concat
            [ "Ill-typed: ", prettyString term, "\n"
            , "Due to: ", prettyString err
            ]

assertFreshIllTyped :: HasCallStack => Fresh (Term TyName Name ()) -> Assertion
assertFreshIllTyped getTerm =
    let term = unsafeRunFresh getTerm in
        case typecheckTerm term of
            Nothing -> assertFailure $ "Well-typed: " ++ prettyString term
            Just _  -> return ()

typecheckProgram :: Program TyName Name () -> Maybe Error
typecheckProgram
    = either Just (\_ -> Nothing)
    . printType
    . Bsl.fromStrict
    . Text.encodeUtf8
    . prettyText

typecheckTerm :: Term TyName Name () -> Maybe Error
typecheckTerm = typecheckProgram . Program () (Version () 0 1 0)

typecheckFreshTerm :: Fresh (Term TyName Name ()) -> Maybe Error
typecheckFreshTerm = typecheckTerm . unsafeRunFresh

-- | Self-application. An example of ill-typed term.
--
-- > /\ (A :: *) -> \(x : A) -> x x
getBuiltinSelfApply :: Fresh (Term TyName Name ())
getBuiltinSelfApply = do
    a <- freshTyName () "a"
    x <- freshName () "x"
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        . Apply () (Var () x)
        $ Var () x
