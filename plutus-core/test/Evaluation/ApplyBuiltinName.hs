-- | Constant application tests.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}

module Evaluation.ApplyBuiltinName
    ( test_applyStaticBuiltinName
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModel)
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Generators
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty

import qualified Data.ByteString.Lazy                                       as BSL
import qualified Data.ByteString.Lazy.Hash                                  as Hash
import           Data.Coerce
import           Hedgehog                                                   hiding (Var)
import           Test.Tasty
import           Test.Tasty.Hedgehog


-- A monad to keep `applyStaticBuiltinName` happy.
-- We can't use CekM or CkM because their exception types don't match Term.

type TestEvaluationException uni =
    EvaluationException () () (Term TyName Name uni ())

type TestM uni = Either (TestEvaluationException uni)

instance SpendBudget (TestM uni) (Term TyName Name uni ()) where
    builtinCostParams = pure defaultCostModel
    spendBudget _key _budget = pure ()

-- | This a generic property-based testing procedure for 'applyBuiltinName'.
-- It generates Haskell values of builtin types (see 'TypedBuiltin' for the list of such types)
-- An argument is generated as a Haskell value, then coerced to the corresponding PLC value which
-- gets appended to the spine of arguments 'applyBuiltinName' expects.
-- The generated Haskell value is passed to the semantics of the 'TypedBuiltinName'
-- (the first argument), i.e. to the second argument. Thus we collect arguments on the PLC side
-- and supply them to a function on the Haskell side. When all appropriate arguments are generated,
-- we check that the results of the two computations match. We also check that each
-- underapplication on the PLC side is a stuck application.
prop_applyStaticBuiltinName
    :: (uni ~ DefaultUni, KnownType (Plain Term uni) r, PrettyConst r)
    => TypedStaticBuiltinName (Plain Term uni) as r
       -- ^ A (typed) builtin name to apply.
    -> FoldArgs as r
       -- ^ The semantics of the builtin name. E.g. the semantics of
       -- 'AddInteger' (and hence 'typedAddInteger') is '(+)'.
    -> Property
prop_applyStaticBuiltinName tbn op = property $ do
    let denot = denoteTypedStaticBuiltinName tbn staticBuiltinNameAsTerm op
        getIterAppValue = runPlcT genTypedBuiltinDef $ genIterAppValue denot
    IterAppValue _ iterApp y <- forAllPrettyPlcT getIterAppValue
    let IterApp name spine = iterApp
        app = applyStaticBuiltinName @(TestM DefaultUni) name
--    traverse_ (\prefix -> app prefix === Right ConstAppStuck) . init $ inits spine
--    app spine === Right (evaluationConstAppResult $ makeKnown y)
    app spine === Right (makeKnown y)

test_typedAddInteger :: TestTree
test_typedAddInteger
    = testProperty "typedAddInteger"
    $ prop_applyStaticBuiltinName typedAddInteger (+)

test_typedSubtractInteger :: TestTree
test_typedSubtractInteger
    = testProperty "typedSubtractInteger"
    $ prop_applyStaticBuiltinName typedSubtractInteger (-)

test_typedMultiplyInteger :: TestTree
test_typedMultiplyInteger
    = testProperty "typedMultiplyInteger"
    $ prop_applyStaticBuiltinName typedMultiplyInteger (*)

test_typedDivideInteger :: TestTree
test_typedDivideInteger
    = testProperty "typedDivideInteger"
    $ prop_applyStaticBuiltinName typedDivideInteger (nonZeroArg div)

test_typedQuotientInteger :: TestTree
test_typedQuotientInteger
    = testProperty "typedQuotientInteger"
    $ prop_applyStaticBuiltinName typedQuotientInteger (nonZeroArg quot)

test_typedModInteger :: TestTree
test_typedModInteger
    = testProperty "typedModInteger"
    $ prop_applyStaticBuiltinName typedModInteger (nonZeroArg mod)

test_typedRemainderInteger :: TestTree
test_typedRemainderInteger
    = testProperty "typedRemainderInteger"
    $ prop_applyStaticBuiltinName typedRemainderInteger (nonZeroArg rem)

test_typedLessThanInteger :: TestTree
test_typedLessThanInteger
    = testProperty "typedLessThanInteger"
    $ prop_applyStaticBuiltinName typedLessThanInteger (<)

test_typedLessThanEqInteger :: TestTree
test_typedLessThanEqInteger
    = testProperty "typedLessThanEqInteger"
    $ prop_applyStaticBuiltinName typedLessThanEqInteger (<=)

test_typedGreaterThanInteger :: TestTree
test_typedGreaterThanInteger
    = testProperty "typedGreaterThanInteger"
    $ prop_applyStaticBuiltinName typedGreaterThanInteger (>)

test_typedGreaterThanEqInteger :: TestTree
test_typedGreaterThanEqInteger
    = testProperty "typedGreaterThanEqInteger"
    $ prop_applyStaticBuiltinName typedGreaterThanEqInteger (>=)

test_typedEqInteger :: TestTree
test_typedEqInteger
    = testProperty "typedEqInteger"
    $ prop_applyStaticBuiltinName typedEqInteger (==)

test_typedConcatenate :: TestTree
test_typedConcatenate
    = testProperty "typedConcatenate"
    $ prop_applyStaticBuiltinName typedConcatenate (<>)

test_typedTakeByteString :: TestTree
test_typedTakeByteString
    = testProperty "typedTakeByteString"
    $ prop_applyStaticBuiltinName typedTakeByteString (coerce BSL.take . integerToInt64)

test_typedSHA2 :: TestTree
test_typedSHA2
    = testProperty "typedSHA2"
    $ prop_applyStaticBuiltinName typedSHA2 (coerce Hash.sha2)

test_typedSHA3 :: TestTree
test_typedSHA3
    = testProperty "typedSHA3"
    $ prop_applyStaticBuiltinName typedSHA3 (coerce Hash.sha3)

test_typedDropByteString :: TestTree
test_typedDropByteString
    = testProperty "typedDropByteString"
    $ prop_applyStaticBuiltinName typedDropByteString (coerce BSL.drop . integerToInt64)

test_typedEqByteString :: TestTree
test_typedEqByteString
    = testProperty "typedEqByteString"
    $ prop_applyStaticBuiltinName typedEqByteString (==)

test_applyStaticBuiltinName :: TestTree
test_applyStaticBuiltinName =
    testGroup "applyStaticBuiltinName"
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
