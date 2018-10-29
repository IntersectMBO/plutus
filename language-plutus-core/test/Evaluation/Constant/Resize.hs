-- | This module tests resizing PLC functions: @resizeInteger@ and @resizeByteString@.

module Evaluation.Constant.Resize
    ( test_resize
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.CkMachine
import           Language.PlutusCore.Generators
import           Language.PlutusCore.MkPlc
import           PlutusPrelude

import           Hedgehog                                 hiding (Size)
import qualified Hedgehog.Gen                             as Gen
import qualified Hedgehog.Range                           as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- | Generate an 'Integer' (represented as a 'Term') and its minimal possible size.
genSizedBuiltinInt :: Gen (TermOf Size)
genSizedBuiltinInt = do
    prevSize <- Gen.integral $ Range.linear 1 5
    let size = succ prevSize
        (prevLow, prevHigh) = toInclusiveBoundsInt prevSize
        (low, high) = toInclusiveBoundsInt size
    int <- Gen.choice
        [ Gen.integral $ Range.linear low (prevLow - 1)
        , Gen.integral $ Range.linear (prevHigh + 1) high
        ]
    return $ TermOf (Constant () $ BuiltinInt () size int) size

-- | Generate a 'ByteString' (represented as a 'Term') and its size.
genSizedBuiltinBS :: Gen (TermOf Size)
genSizedBuiltinBS = do
    size <- Gen.integral $ Range.linear 2 10
    bs <- genLowerBytes $ Range.linear (fromIntegral size) (fromIntegral size)
    return $ TermOf (Constant () $ BuiltinBS () size bs) size

-- | Resize a 'Term' using some resizing 'BuiltinName' and a function that alters a size.
resizeTermOfSize :: BuiltinName -> (Size -> Size) -> TermOf Size -> TermOf Size
resizeTermOfSize resize f (TermOf term size) = TermOf resizedTerm size' where
    size' = f size
    resizedTerm =
        mkIterApp (mkIterInst (builtinNameAsTerm resize) [TyInt () size, TyInt () size'])
            [ Constant () $ BuiltinSize () size'
            , term
            ]

-- | Generate a @TermOf a@ using for showing the 'PrettyPlc' instance for 'Term' and
-- the 'Pretty' instance for @a@.
allTermOf :: (Monad m, Pretty a) => Gen (TermOf a) -> PropertyT m (TermOf a)
allTermOf genSizedTerm =
    fmap unPrettyConfigIgnore <$> forAllPrettyPlc (fmap PrettyConfigIgnore <$> genSizedTerm)

-- | Check that resizing an @integer@ to a bigger size than the minimal possible size of
-- this @integer@ does not result in 'EvaluationFailure'.
prop_resizeIntegerSuccess :: Property
prop_resizeIntegerSuccess = property $ do
    sizedTerm <- allTermOf genSizedBuiltinInt
    sizeDelta <- forAll . Gen.integral $ Range.linear 1 10
    let resizedTerm = _termOfTerm $ resizeTermOfSize ResizeInteger (+ sizeDelta) sizedTerm
    evaluateCk resizedTerm /== EvaluationFailure

-- | Check that resizing a @integer@ to a smaller size than the minimal possible size of
-- this @integer@ results in 'EvaluationFailure'.
prop_resizeIntegerFailure :: Property
prop_resizeIntegerFailure = property $ do
    sizedTerm@(TermOf _ size) <- allTermOf genSizedBuiltinInt
    sizeDelta <- forAll . Gen.integral $ Range.linear 1 (size - 1)
    let resizedTerm = _termOfTerm $ resizeTermOfSize ResizeInteger (subtract sizeDelta) sizedTerm
    evaluateCk resizedTerm === EvaluationFailure

-- | Check that resizing a @integer@ to a bigger size than the minimal possible size of
-- this @bytestring@ does not result in 'EvaluationFailure'.
prop_resizeByteStringSuccess :: Property
prop_resizeByteStringSuccess = property $ do
    sizedTerm <- allTermOf genSizedBuiltinBS
    sizeDelta <- forAll . Gen.integral $ Range.linear 1 10
    let resizedTerm = _termOfTerm $ resizeTermOfSize ResizeByteString (+ sizeDelta) sizedTerm
    evaluateCk resizedTerm /== EvaluationFailure

-- | Check that resizing a @bytestring@ to a smaller size than the minimal possible size of
-- this @bytestring@ results in 'EvaluationFailure'.
prop_resizeByteStringFailure :: Property
prop_resizeByteStringFailure = property $ do
    sizedTerm@(TermOf _ size) <- allTermOf genSizedBuiltinBS
    sizeDelta <- forAll . Gen.integral $ Range.linear 1 (size - 1)
    let resizedTerm =_termOfTerm $ resizeTermOfSize ResizeByteString (subtract sizeDelta) sizedTerm
    evaluateCk resizedTerm === EvaluationFailure

-- | Check that resizing an @integer@ to a bigger size than the minimal possible size of
-- this @integer@ and then resizing back does not result in 'EvaluationFailure'.
prop_reresizeIntegerSuccess :: Property
prop_reresizeIntegerSuccess = property $ do
    sizedTerm <- allTermOf genSizedBuiltinInt
    sizeDelta <- forAll . Gen.integral $ Range.linear 1 10
    let resizedTerm
            = _termOfTerm
            . resizeTermOfSize ResizeInteger (subtract sizeDelta)
            . resizeTermOfSize ResizeInteger (+ sizeDelta)
            $ sizedTerm
    evaluateCk resizedTerm /== EvaluationFailure

-- | Check that resizing a @integer@ to a smaller size than the minimal possible size of
-- this @integer@ and then resizing back still results in 'EvaluationFailure'.
prop_reresizeIntegerFailure :: Property
prop_reresizeIntegerFailure = property $ do
    sizedTerm@(TermOf _ size) <- allTermOf genSizedBuiltinInt
    sizeDelta <- forAll . Gen.integral $ Range.linear 1 (size - 1)
    let resizedTerm
            = _termOfTerm
            . resizeTermOfSize ResizeInteger (+ sizeDelta)
            . resizeTermOfSize ResizeInteger (subtract sizeDelta)
            $ sizedTerm
    evaluateCk resizedTerm === EvaluationFailure

-- | Check that resizing an @bytestring@ to a bigger size than the minimal possible size of
-- this @bytestring@ and then resizing back does not result in 'EvaluationFailure'.
prop_reresizeByteStringSuccess :: Property
prop_reresizeByteStringSuccess = property $ do
    sizedTerm <- allTermOf genSizedBuiltinBS
    sizeDelta <- forAll . Gen.integral $ Range.linear 1 10
    let resizedTerm
            = _termOfTerm
            . resizeTermOfSize ResizeByteString (subtract sizeDelta)
            . resizeTermOfSize ResizeByteString (+ sizeDelta)
            $ sizedTerm
    evaluateCk resizedTerm /== EvaluationFailure

-- | Check that resizing a @bytestring@ to a smaller size than the minimal possible size of
-- this @bytestring@ and then resizing back still results in 'EvaluationFailure'.
prop_reresizeByteStringFailure :: Property
prop_reresizeByteStringFailure = property $ do
    sizedTerm@(TermOf _ size) <- allTermOf genSizedBuiltinBS
    sizeDelta <- forAll . Gen.integral $ Range.linear 1 (size - 1)
    let resizedTerm
            = _termOfTerm
            . resizeTermOfSize ResizeByteString (+ sizeDelta)
            . resizeTermOfSize ResizeByteString (subtract sizeDelta)
            $ sizedTerm
    evaluateCk resizedTerm === EvaluationFailure

test_resizeInteger :: TestTree
test_resizeInteger =
    testGroup "resizeInteger"
        [ testProperty "resizeInteger_Success"   prop_resizeIntegerSuccess
        , testProperty "resizeInteger_Failure"   prop_resizeIntegerFailure
        , testProperty "reresizeInteger_Failure" prop_reresizeIntegerFailure
        , testProperty "reresizeInteger_Success" prop_reresizeIntegerSuccess
        ]

test_resizeByteString :: TestTree
test_resizeByteString =
    testGroup "resizeByteString"
        [ testProperty "resizeByteString_Success"   prop_resizeByteStringSuccess
        , testProperty "resizeByteString_Failure"   prop_resizeByteStringFailure
        , testProperty "reresizeByteString_Failure" prop_reresizeByteStringFailure
        , testProperty "reresizeByteString_Success" prop_reresizeByteStringSuccess
        ]

test_resize :: TestTree
test_resize =
    testGroup "resize"
        [ test_resizeInteger
        , test_resizeByteString
        ]
