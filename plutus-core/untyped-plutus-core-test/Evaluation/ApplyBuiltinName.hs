{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}

module Evaluation.ApplyBuiltin
    ( test_applyStaticBuiltin
    ) where

import           PlutusPrelude

import           Language.UntypedPlutusCore

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Generators
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Control.Monad.Except
import qualified Data.ByteString                                            as BS
import qualified Data.ByteString.Hash                                       as Hash
import           Data.Proxy
import           Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- | A simplified (because we don't need the full generality here) version of
-- 'Language.PlutusCore.Generators.Internal.Entity.genIterAppValue'.
genArgsRes
    :: Generatable uni
    => TypeScheme (Term Name uni fun ()) as res -> FoldArgs as res -> Gen ([Term Name uni fun ()], res)
genArgsRes (TypeSchemeResult _)     y = return ([], y)
genArgsRes (TypeSchemeArrow _ schB) f = do
    TermOf v x <- genTypedBuiltinDef AsKnownType
    first (v :) <$> genArgsRes schB (f x)
genArgsRes (TypeSchemeAll _ _ schK) f = genArgsRes (schK Proxy) f

type AppErr = EvaluationException () () (Term Name DefaultUni () ())

-- | A simple monad for evaluating constant applications in.
newtype AppM a = AppM
    { unAppM :: Either AppErr a
    } deriving newtype (Functor, Applicative, Monad, MonadError AppErr)

instance SpendBudget AppM () (Term Name DefaultUni () ()) where
    spendBudget _ _ = pure ()
    builtinCostParams = pure defaultCostModel

-- | This shows that the builtin application machinery accepts untyped terms.
prop_applyStaticBuiltin
    :: (KnownType (Term Name DefaultUni () ()) res)
    => TypedStaticBuiltin (Term Name DefaultUni () ()) args res
       -- ^ A (typed) builtin name to apply.
    -> FoldArgs args res
       -- ^ The semantics of the builtin name. E.g. the semantics of
       -- 'AddInteger' (and hence 'typedAddInteger') is '(+)'.
    -> Property
prop_applyStaticBuiltin (TypedStaticBuiltin name sch) op = property $ do
    (args, res) <- forAllNoShow $ genArgsRes sch op
    let rhs = makeKnown res
    case unAppM $ applyStaticBuiltin name args of
        Left _    -> fail $ "Failure while checking an application of " ++ show name
        Right lhs -> lhs === rhs

test_typedAddInteger :: TestTree
test_typedAddInteger
    = testProperty "typedAddInteger"
    $ prop_applyStaticBuiltin typedAddInteger (+)

test_typedSubtractInteger :: TestTree
test_typedSubtractInteger
    = testProperty "typedSubtractInteger"
    $ prop_applyStaticBuiltin typedSubtractInteger (-)

test_typedMultiplyInteger :: TestTree
test_typedMultiplyInteger
    = testProperty "typedMultiplyInteger"
    $ prop_applyStaticBuiltin typedMultiplyInteger (*)

test_typedDivideInteger :: TestTree
test_typedDivideInteger
    = testProperty "typedDivideInteger"
    $ prop_applyStaticBuiltin typedDivideInteger (nonZeroArg div)

test_typedQuotientInteger :: TestTree
test_typedQuotientInteger
    = testProperty "typedQuotientInteger"
    $ prop_applyStaticBuiltin typedQuotientInteger (nonZeroArg quot)

test_typedModInteger :: TestTree
test_typedModInteger
    = testProperty "typedModInteger"
    $ prop_applyStaticBuiltin typedModInteger (nonZeroArg mod)

test_typedRemainderInteger :: TestTree
test_typedRemainderInteger
    = testProperty "typedRemainderInteger"
    $ prop_applyStaticBuiltin typedRemainderInteger (nonZeroArg rem)

test_typedLessThanInteger :: TestTree
test_typedLessThanInteger
    = testProperty "typedLessThanInteger"
    $ prop_applyStaticBuiltin typedLessThanInteger (<)

test_typedLessThanEqInteger :: TestTree
test_typedLessThanEqInteger
    = testProperty "typedLessThanEqInteger"
    $ prop_applyStaticBuiltin typedLessThanEqInteger (<=)

test_typedGreaterThanInteger :: TestTree
test_typedGreaterThanInteger
    = testProperty "typedGreaterThanInteger"
    $ prop_applyStaticBuiltin typedGreaterThanInteger (>)

test_typedGreaterThanEqInteger :: TestTree
test_typedGreaterThanEqInteger
    = testProperty "typedGreaterThanEqInteger"
    $ prop_applyStaticBuiltin typedGreaterThanEqInteger (>=)

test_typedEqInteger :: TestTree
test_typedEqInteger
    = testProperty "typedEqInteger"
    $ prop_applyStaticBuiltin typedEqInteger (==)

test_typedConcatenate :: TestTree
test_typedConcatenate
    = testProperty "typedConcatenate"
    $ prop_applyStaticBuiltin typedConcatenate (<>)

test_typedTakeByteString :: TestTree
test_typedTakeByteString
    = testProperty "typedTakeByteString"
    $ prop_applyStaticBuiltin typedTakeByteString (BS.take . integerToInt)

test_typedSHA2 :: TestTree
test_typedSHA2
    = testProperty "typedSHA2"
    $ prop_applyStaticBuiltin typedSHA2 Hash.sha2

test_typedSHA3 :: TestTree
test_typedSHA3
    = testProperty "typedSHA3"
    $ prop_applyStaticBuiltin typedSHA3 Hash.sha3

test_typedDropByteString :: TestTree
test_typedDropByteString
    = testProperty "typedDropByteString"
    $ prop_applyStaticBuiltin typedDropByteString (BS.drop . integerToInt)

test_typedEqByteString :: TestTree
test_typedEqByteString
    = testProperty "typedEqByteString"
    $ prop_applyStaticBuiltin typedEqByteString (==)

test_applyStaticBuiltin :: TestTree
test_applyStaticBuiltin =
    testGroup "applyStaticBuiltin"
        [ test_typedAddInteger
        , test_typedSubtractInteger
        , test_typedMultiplyInteger
        , test_typedDivideInteger
        , test_typedQuotientInteger
        , test_typedModInteger
        , test_typedRemainderInteger
        , test_typedLessThanInteger
        , test_typedLessThanEqInteger
        , test_typedGreaterThanInteger
        , test_typedGreaterThanEqInteger
        , test_typedEqInteger
        , test_typedConcatenate
        , test_typedTakeByteString
        , test_typedDropByteString
        , test_typedEqByteString
        , test_typedSHA2
        , test_typedSHA3
        ]
