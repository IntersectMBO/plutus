{-# LANGUAGE OverloadedStrings #-}
module Evaluation.TypeCheck
    ( test_typecheck
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.ChurchNat
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit

import qualified Data.ByteString.Lazy                      as Bsl
import           Data.Foldable
import qualified Data.Text.Encoding                        as Text
import           Test.Tasty
import           Test.Tasty.HUnit

-- | Assert a 'Term' is well-typed.
assertQuoteWellTyped :: HasCallStack => Quote (Term TyName Name ()) -> Assertion
assertQuoteWellTyped getTerm =
    let term = runQuote getTerm in
        for_ (typecheckTerm term) $ \err -> assertFailure $ concat
            [ "Ill-typed: ", prettyCfgString term, "\n"
            , "Due to: ", prettyCfgString err
            ]

-- | Assert a term is ill-typed.
assertQuoteIllTyped :: HasCallStack => Quote (Term TyName Name ()) -> Assertion
assertQuoteIllTyped getTerm =
    let term = runQuote getTerm in
        case typecheckTerm term of
            Nothing -> assertFailure $ "Well-typed: " ++ prettyCfgString term
            Just _  -> return ()

typecheckTerm :: Term TyName Name () -> Maybe (Error AlexPosn)
typecheckTerm = typecheckProgram . Program () (Version () 0 1 0)

typecheckProgram :: Program TyName Name () -> Maybe (Error AlexPosn)
typecheckProgram
    = either Just (\_ -> Nothing)
    . printType
    . Bsl.fromStrict
    . Text.encodeUtf8
    . prettyCfgText

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
