-- | Constant application tests.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}

module Evaluation.ApplyBuiltinName
    ( test_applyBuiltinName
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Generators
import           Language.PlutusCore.Pretty

import qualified Data.ByteString.Lazy                            as BSL
import qualified Data.ByteString.Lazy.Hash                       as Hash
import           Data.Coerce
import           Data.Foldable
import           Data.List
import           Hedgehog                                        hiding (Var)
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- | This a generic property-based testing procedure for 'applyBuiltinName'.
-- It generates Haskell values of builtin types (see 'TypedBuiltin' for the list of such types)
-- An argument is generated as a Haskell value, then coerced to the corresponding PLC value which
-- gets appended to the spine of arguments 'applyBuiltinName' expects.
-- The generated Haskell value is passed to the semantics of the 'TypedBuiltinName'
-- (the first argument), i.e. to the second argument. Thus we collect arguments on the PLC side
-- and supply them to a function on the Haskell side. When all appropriate arguments are generated,
-- we check that the results of the two computations match. We also check that each
-- underapplication on the PLC side is a stuck application.
prop_applyBuiltinName
    :: (uni ~ DefaultUni, KnownType (Plain Term uni) r, PrettyConst r)
    => TypedBuiltinName (Plain Term uni) as r
       -- ^ A (typed) builtin name to apply.
    -> FoldArgs as r
       -- ^ The semantics of the builtin name. E.g. the semantics of
       -- 'AddInteger' (and hence 'typedAddInteger') is '(+)'.
    -> TypedBuiltinGenT uni IO
       -- ^ How to generate values of builtin types.
    -> Property
prop_applyBuiltinName tbn op allTbs = property $ do
    let getIterAppValue = runPlcT allTbs . genIterAppValue $ denoteTypedBuiltinName tbn op
    IterAppValue _ iterApp y <- forAllPrettyPlcT getIterAppValue
    let IterApp name spine = iterApp
        app = applyBuiltinName @(CkM DefaultUni) name
    traverse_ (\prefix -> app prefix === Right ConstAppStuck) . init $ inits spine
    app spine === Right (evaluationConstAppResult $ makeKnown y)

test_typedAddInteger :: TestTree
test_typedAddInteger
    = testProperty "typedAddInteger"
    $ prop_applyBuiltinName typedAddInteger (+)
    $ genTypedBuiltinDef

test_typedSubtractInteger :: TestTree
test_typedSubtractInteger
    = testProperty "typedSubtractInteger"
    $ prop_applyBuiltinName typedSubtractInteger (-)
    $ genTypedBuiltinDef

test_typedMultiplyInteger :: TestTree
test_typedMultiplyInteger
    = testProperty "typedMultiplyInteger"
    $ prop_applyBuiltinName typedMultiplyInteger (*)
    $ genTypedBuiltinDef

test_typedDivideInteger :: TestTree
test_typedDivideInteger
    = testProperty "typedDivideInteger"
    $ prop_applyBuiltinName typedDivideInteger (nonZeroArg div)
    $ genTypedBuiltinDivide

test_typedQuotientInteger :: TestTree
test_typedQuotientInteger
    = testProperty "typedQuotientInteger"
    $ prop_applyBuiltinName typedQuotientInteger (nonZeroArg quot)
    $ genTypedBuiltinDivide

test_typedModInteger :: TestTree
test_typedModInteger
    = testProperty "typedModInteger"
    $ prop_applyBuiltinName typedModInteger (nonZeroArg mod)
    $ genTypedBuiltinDivide

test_typedRemainderInteger :: TestTree
test_typedRemainderInteger
    = testProperty "typedRemainderInteger"
    $ prop_applyBuiltinName typedRemainderInteger (nonZeroArg rem)
    $ genTypedBuiltinDivide

test_typedLessThanInteger :: TestTree
test_typedLessThanInteger
    = testProperty "typedLessThanInteger"
    $ prop_applyBuiltinName typedLessThanInteger (<)
    $ genTypedBuiltinDef

test_typedLessThanEqInteger :: TestTree
test_typedLessThanEqInteger
    = testProperty "typedLessThanEqInteger"
    $ prop_applyBuiltinName typedLessThanEqInteger (<=)
    $ genTypedBuiltinDef

test_typedGreaterThanInteger :: TestTree
test_typedGreaterThanInteger
    = testProperty "typedGreaterThanInteger"
    $ prop_applyBuiltinName typedGreaterThanInteger (>)
    $ genTypedBuiltinDef

test_typedGreaterThanEqInteger :: TestTree
test_typedGreaterThanEqInteger
    = testProperty "typedGreaterThanEqInteger"
    $ prop_applyBuiltinName typedGreaterThanEqInteger (>=)
    $ genTypedBuiltinDef

test_typedEqInteger :: TestTree
test_typedEqInteger
    = testProperty "typedEqInteger"
    $ prop_applyBuiltinName typedEqInteger (==)
    $ genTypedBuiltinDef

test_typedConcatenate :: TestTree
test_typedConcatenate
    = testProperty "typedConcatenate"
    $ prop_applyBuiltinName typedConcatenate (<>)
    $ genTypedBuiltinDef

test_typedTakeByteString :: TestTree
test_typedTakeByteString
    = testProperty "typedTakeByteString"
    $ prop_applyBuiltinName typedTakeByteString (coerce BSL.take . integerToInt64)
    $ genTypedBuiltinDef

test_typedSHA2 :: TestTree
test_typedSHA2
    = testProperty "typedSHA2"
    $ prop_applyBuiltinName typedSHA2 (coerce Hash.sha2)
    $ genTypedBuiltinDef

test_typedSHA3 :: TestTree
test_typedSHA3
    = testProperty "typedSHA3"
    $ prop_applyBuiltinName typedSHA3 (coerce Hash.sha3)
    $ genTypedBuiltinDef

test_typedDropByteString :: TestTree
test_typedDropByteString
    = testProperty "typedDropByteString"
    $ prop_applyBuiltinName typedDropByteString (coerce BSL.drop . integerToInt64)
    $ genTypedBuiltinDef

test_typedEqByteString :: TestTree
test_typedEqByteString
    = testProperty "typedEqByteString"
    $ prop_applyBuiltinName typedEqByteString (==)
    $ genTypedBuiltinDef

test_applyBuiltinName :: TestTree
test_applyBuiltinName =
    testGroup "applyBuiltinName"
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
