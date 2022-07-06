-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Werror #-}

module Evaluation.Builtins.Bitwise (
  bitwiseAndCommutes,
  bitwiseIorCommutes,
  bitwiseXorCommutes,
  bitwiseAndIdentity,
  bitwiseIorIdentity,
  bitwiseXorIdentity,
  bitwiseAndAbsorbing,
  bitwiseIorAbsorbing,
  bitwiseXorComplement,
  bitwiseAndSelf,
  bitwiseIorSelf,
  bitwiseXorSelf,
  bitwiseAndAssociates,
  bitwiseIorAssociates,
  bitwiseXorAssociates,
  bitwiseComplementSelfInverts,
  bitwiseAndDeMorgan,
  bitwiseIorDeMorgan,
  popCountSingleByte,
  popCountAppend,
  testBitEmpty,
  testBitSingleByte,
  testBitAppend,
  writeBitRead,
  writeBitDouble,
  writeBitAgreement,
  ffsSingleByte,
  ffsAppend,
  rotateIdentity,
  rotateIndexMotion,
  rotateHomogenous,
  rotateSum,
  shiftIdentity,
  shiftIndexMotion,
  shiftHomogenous,
  shiftSum,
  iToBsRoundtrip,
  bsToITrailing,
  bsToIHomogenous,
  ) where

import Control.Lens.Fold (Fold, folding, has, hasn't, preview)
import Control.Monad (guard)
import Data.Bitraversable (bitraverse)
import Data.Bits (bit, complement, countTrailingZeros, popCount, shiftL, xor, zeroBits, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Word (Word8)
import Evaluation.Builtins.Common (typecheckEvaluateCek)
import GHC.Exts (fromListN, toList)
import Hedgehog (Gen, PropertyT, Range, annotate, annotateShow, cover, evalEither, failure, forAllWith, success, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore (DefaultFun (AddInteger, AndByteString, AppendByteString, ByteStringToInteger, ComplementByteString, FindFirstSetByteString, IntegerToByteString, IorByteString, PopCountByteString, RotateByteString, ShiftByteString, TestBitByteString, WriteBitByteString, XorByteString),
                   DefaultUni, Error, EvaluationResult (EvaluationFailure, EvaluationSuccess), Name, Term)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterApp)
import Text.Show.Pretty (ppShow)
import UntypedPlutusCore qualified as Untyped

bitwiseIorCommutes :: PropertyT IO ()
bitwiseIorCommutes = commutative (.|.) IorByteString

bitwiseAndCommutes :: PropertyT IO ()
bitwiseAndCommutes = commutative (.&.) AndByteString

bitwiseXorCommutes :: PropertyT IO ()
bitwiseXorCommutes = commutative xor XorByteString

bitwiseAndIdentity :: PropertyT IO ()
bitwiseAndIdentity = identity (complement zeroBits) AndByteString

bitwiseIorIdentity :: PropertyT IO ()
bitwiseIorIdentity = identity zeroBits IorByteString

bitwiseXorIdentity :: PropertyT IO ()
bitwiseXorIdentity = identity zeroBits XorByteString

bitwiseAndAbsorbing :: PropertyT IO ()
bitwiseAndAbsorbing = absorbing zeroBits AndByteString

bitwiseIorAbsorbing :: PropertyT IO ()
bitwiseIorAbsorbing = absorbing (complement zeroBits) IorByteString

bitwiseXorComplement :: PropertyT IO ()
bitwiseXorComplement = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  let len = BS.length bs
  let allOnes = BS.replicate len . complement $ zeroBits
  outcome1 <- goXor bs allOnes
  outcome2 <- goComplement bs
  case (outcome1, outcome2) of
    (EvaluationSuccess res1, EvaluationSuccess res2) -> res1 === res2
    _                                                -> failure
  where
    goXor ::
      ByteString ->
      ByteString ->
      PropertyT IO (EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()))
    goXor leftArg rightArg = do
      let leftArg' = mkConstant @ByteString () leftArg
      let rightArg' = mkConstant @ByteString () rightArg
      let comp = mkIterApp () (builtin () XorByteString) [leftArg', rightArg']
      cekEval comp
    goComplement ::
      ByteString ->
      PropertyT IO (EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()))
    goComplement bs = do
      let bs' = mkConstant @ByteString () bs
      let comp = mkIterApp () (builtin () ComplementByteString) [bs']
      cekEval comp

bitwiseAndSelf :: PropertyT IO ()
bitwiseAndSelf = self AndByteString

bitwiseIorSelf :: PropertyT IO ()
bitwiseIorSelf = self IorByteString

bitwiseXorSelf :: PropertyT IO ()
bitwiseXorSelf = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  let len = BS.length bs
  let bs' = mkConstant @ByteString () bs
  let expected = mkConstant @ByteString () . BS.replicate len $ zeroBits
  let comp = mkIterApp () (builtin () XorByteString) [bs', bs']
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === expected
    _                     -> failure

bitwiseAndAssociates :: PropertyT IO ()
bitwiseAndAssociates = associative (.&.) AndByteString

bitwiseIorAssociates :: PropertyT IO ()
bitwiseIorAssociates = associative (.|.) IorByteString

bitwiseXorAssociates :: PropertyT IO ()
bitwiseXorAssociates = associative xor XorByteString

bitwiseComplementSelfInverts :: PropertyT IO ()
bitwiseComplementSelfInverts = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  let bs' = mkConstant @ByteString () bs
  let comp = mkIterApp () (builtin () ComplementByteString) [
        mkIterApp () (builtin () ComplementByteString) [bs']
        ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === mkConstant () bs
    _                     -> failure

bitwiseAndDeMorgan :: PropertyT IO ()
bitwiseAndDeMorgan = demorgan AndByteString IorByteString

bitwiseIorDeMorgan :: PropertyT IO ()
bitwiseIorDeMorgan = demorgan IorByteString AndByteString

popCountSingleByte :: PropertyT IO ()
popCountSingleByte = do
  w8 <- forAllWith ppShow Gen.enumBounded
  let bs = BS.singleton w8
  let expected :: Integer = fromIntegral . popCount $ w8
  let comp = mkIterApp () (builtin () PopCountByteString) [
        mkConstant @ByteString () bs
        ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === mkConstant () expected
    _                     -> failure

popCountAppend :: PropertyT IO ()
popCountAppend = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  bs' <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  let arg1 = mkConstant @ByteString () bs
  let arg2 = mkConstant @ByteString () bs'
  let comp1 = mkIterApp () (builtin () PopCountByteString) [
        mkIterApp () (builtin () AppendByteString) [arg1, arg2]
        ]
  let comp2 = mkIterApp () (builtin () AddInteger) [
        mkIterApp () (builtin () PopCountByteString) [arg1],
        mkIterApp () (builtin () PopCountByteString) [arg2]
        ]
  outcome <- bitraverse cekEval cekEval (comp1, comp2)
  case outcome of
    (EvaluationSuccess res, EvaluationSuccess res') -> res === res'
    _                                               -> failure

testBitEmpty :: PropertyT IO ()
testBitEmpty = do
  ix <- forAllWith ppShow . Gen.integral $ indexRange
  let arg = mkConstant @ByteString () ""
  let comp = mkIterApp () (builtin () TestBitByteString) [
        arg,
        mkConstant @Integer () ix
        ]
  outcome <- cekEval comp
  case outcome of
    EvaluationFailure -> success
    _                 -> failure

testBitSingleByte :: PropertyT IO ()
testBitSingleByte = do
  w8 <- forAllWith ppShow Gen.enumBounded
  let bs = BS.singleton w8
  ix <- forAllWith ppShow . Gen.integral . indexRangeOf $ 8
  cover 45 "out of bounds" $ ix < 0 || ix >= 8
  cover 45 "in-bounds" $ 0 <= ix && ix < 8
  let expected = bitAt w8 ix
  let comp = mkIterApp () (builtin () TestBitByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () ix
        ]
  outcome <- cekEval comp
  case (expected, outcome) of
    (Nothing, EvaluationFailure)    -> success
    (Just b, EvaluationSuccess res) -> res === mkConstant @Bool () b
    _                               -> failure

testBitAppend :: PropertyT IO ()
testBitAppend = do
  testCase <- forAllWith ppShow genBitAppendCase
  cover 30 "out of bounds" . appendOutOfBounds $ testCase
  cover 30 "in-bounds, first argument" . appendInBoundsFirst $ testCase
  cover 30 "in-bounds, second argument" . appendInBoundsSecond $ testCase
  let (x, y, ix) = getBitAppendArgs testCase
  let arg1 = mkConstant @ByteString () x
  let arg2 = mkConstant @ByteString () y
  let argIx = mkConstant @Integer () ix
  let comp = mkIterApp () (builtin () TestBitByteString) [
        mkIterApp () (builtin () AppendByteString) [arg1, arg2],
        argIx
        ]
  let comp' = go x y ix
  outcome <- bitraverse cekEval cekEval (comp, comp')
  case outcome of
    (EvaluationFailure, EvaluationFailure) -> success
    (EvaluationSuccess res, EvaluationSuccess res') -> do
      annotateShow res
      annotateShow res'
      res === res'
    _ -> failure
  where
    go ::
      ByteString ->
      ByteString ->
      Integer ->
      Term Untyped.TyName Name DefaultUni DefaultFun ()
    go bs bs' ix = let len' = fromIntegral $ 8 * BS.length bs' in
      case compare ix len' of
        LT -> mkIterApp () (builtin () TestBitByteString) [
                mkConstant @ByteString () bs',
                mkConstant @Integer () ix
                ]
        _ -> mkIterApp () (builtin () TestBitByteString) [
                mkConstant @ByteString () bs,
                mkConstant @Integer () (ix - len')
                ]

writeBitRead :: PropertyT IO ()
writeBitRead = do
  testCase <- forAllWith ppShow genWriteBitCase
  cover 45 "out of bounds" . hasn't _WriteBitResult $ testCase
  cover 45 "in-bounds" . has _WriteBitResult $ testCase
  let (bs, ix, b) = getWriteBitArgs testCase
  let expected = preview _WriteBitResult testCase
  let bs' = mkConstant @ByteString () bs
  let ix' = mkConstant @Integer () ix
  let b' = mkConstant @Bool () b
  let comp = mkIterApp () (builtin () TestBitByteString) [
        mkIterApp () (builtin () WriteBitByteString) [bs', ix', b'],
        ix'
        ]
  outcome <- cekEval comp
  case (expected, outcome) of
    (Nothing, EvaluationFailure)       -> success
    (Just res, EvaluationSuccess res') -> mkConstant @Bool () res === res'
    _                                  -> failure

writeBitDouble :: PropertyT IO ()
writeBitDouble = do
  testCase <- forAllWith ppShow genWriteBitCase
  cover 45 "out of bounds" . hasn't _WriteBitResult $ testCase
  cover 45 "in-bounds" . has _WriteBitResult $ testCase
  let (bs, ix, b) = getWriteBitArgs testCase
  b' <- forAllWith ppShow Gen.enumBounded
  let bs' = mkConstant @ByteString () bs
  let ix' = mkConstant @Integer () ix
  let writeTwice = mkIterApp () (builtin () WriteBitByteString) [
        mkIterApp () (builtin () WriteBitByteString) [bs', ix', mkConstant @Bool () b],
        ix',
        mkConstant @Bool () b'
        ]
  let writeOnce = mkIterApp () (builtin () WriteBitByteString) [
        bs',
        ix',
        mkConstant @Bool () b'
        ]
  outcome <- bitraverse cekEval cekEval (writeTwice, writeOnce)
  case outcome of
    (EvaluationFailure, EvaluationFailure)          -> success
    (EvaluationSuccess res, EvaluationSuccess res') -> res === res'
    _                                               -> failure

writeBitAgreement :: PropertyT IO ()
writeBitAgreement = do
  testCase <- forAllWith ppShow genWriteBitAgreementCase
  let (bs, writeIx, readIx) = getWriteBitAgreementArgs testCase
  cover 45 "read known zero" $ writeIx /= readIx
  cover 45 "read known one" $ writeIx == readIx
  let comp = mkIterApp () (builtin () TestBitByteString) [
          mkIterApp () (builtin () WriteBitByteString) [
            mkConstant @ByteString () bs,
            mkConstant @Integer () writeIx,
            mkConstant @Bool () True
            ],
          mkConstant @Integer () readIx
          ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res ->
      if writeIx == readIx
      then res === mkConstant @Bool () True
      else res === mkConstant @Bool () False
    _ -> failure

ffsSingleByte :: PropertyT IO ()
ffsSingleByte = do
  w8 <- forAllWith ppShow Gen.enumBounded
  let bs = BS.singleton w8
  let expected = case w8 of
        0 -> (-1)
        _ -> fromIntegral . countTrailingZeros $ w8
  let comp = mkIterApp () (builtin () FindFirstSetByteString) [
        mkConstant @ByteString () bs
        ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === mkConstant @Integer () expected
    _                     -> failure

ffsAppend :: PropertyT IO ()
ffsAppend = do
  testCase <- forAllWith ppShow genFFSAppendCase
  let which = ffsAppendType testCase
  cover 30 "both arguments zero" $ which == ZeroBoth
  cover 30 "second argument zero" $ which == ZeroSecond
  cover 30 "second argument nonzero" $ which == NotZeroSecond
  let (bs, bs') = getFFSAppendArgs testCase
  let comp = mkIterApp () (builtin () FindFirstSetByteString) [
        mkIterApp () (builtin () AppendByteString) [
          mkConstant @ByteString () bs,
          mkConstant @ByteString () bs'
          ]
        ]
  let comp' = case which of
        ZeroBoth -> mkConstant @Integer () (-1)
        ZeroSecond -> let bitLen' = fromIntegral $ 8 * BS.length bs' in
          mkIterApp () (builtin () AddInteger) [
            mkIterApp () (builtin () FindFirstSetByteString) [
              mkConstant @ByteString () bs
              ],
            mkConstant @Integer () bitLen'
          ]
        NotZeroSecond -> mkIterApp () (builtin () FindFirstSetByteString) [
            mkConstant @ByteString () bs'
            ]
  outcome <- bitraverse cekEval cekEval (comp, comp')
  case outcome of
    (EvaluationSuccess res, EvaluationSuccess res') -> res === res'
    _                                               -> failure

rotateIdentity :: PropertyT IO ()
rotateIdentity = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  let comp = mkIterApp () (builtin () RotateByteString) [
          mkConstant @ByteString () bs,
          mkConstant @Integer () 0
          ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === mkConstant () bs
    _                     -> failure

shiftIdentity :: PropertyT IO ()
shiftIdentity = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  let comp = mkIterApp () (builtin () ShiftByteString) [
          mkConstant @ByteString () bs,
          mkConstant @Integer () 0
          ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === mkConstant () bs
    _                     -> failure


rotateIndexMotion :: PropertyT IO ()
rotateIndexMotion = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  w8 <- forAllWith ppShow Gen.enumBounded
  let bs' = BS.cons w8 bs
  let bitLen = fromIntegral $ BS.length bs' * 8
  i <- forAllWith ppShow . Gen.integral . indexRangeOf $ bitLen
  readIx <- forAllWith ppShow . Gen.integral . indexRangeFor $ bitLen
  let expectedReadIx = case signum i of
        1 -> let raw = readIx - i in
              case signum raw of
                (-1) -> bitLen + raw
                _    -> raw
        0 -> readIx
        _ -> (readIx - i) `rem` bitLen
  let comp = mkIterApp () (builtin () TestBitByteString) [
        mkIterApp () (builtin () RotateByteString) [
          mkConstant @ByteString () bs',
          mkConstant @Integer () i
          ],
        mkConstant @Integer () readIx
        ]
  let expected = mkIterApp () (builtin () TestBitByteString) [
        mkConstant @ByteString () bs',
        mkConstant @Integer () expectedReadIx
        ]
  outcome <- bitraverse cekEval cekEval (expected, comp)
  case outcome of
    (EvaluationSuccess res, EvaluationSuccess actual) -> res === actual
    _                                                 -> failure

shiftIndexMotion :: PropertyT IO ()
shiftIndexMotion = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  w8 <- forAllWith ppShow Gen.enumBounded
  let bs' = BS.cons w8 bs
  let bitLen = fromIntegral $ BS.length bs' * 8
  i <- forAllWith ppShow . Gen.integral . indexRangeOf $ bitLen
  readIx <- forAllWith ppShow . Gen.integral . indexRangeFor $ bitLen
  let comp = mkIterApp () (builtin () TestBitByteString) [
        mkIterApp () (builtin () ShiftByteString) [
          mkConstant @ByteString () bs',
          mkConstant @Integer () i
          ],
        mkConstant @Integer () readIx
        ]
  let comp' = let expectedIx = readIx - i in
        if | expectedIx < 0 -> mkConstant @Bool () False
           | expectedIx >= bitLen -> mkConstant @Bool () False
           | otherwise -> mkIterApp () (builtin () TestBitByteString) [
                            mkConstant @ByteString () bs',
                            mkConstant @Integer () expectedIx
                            ]
  outcome <- bitraverse cekEval cekEval (comp, comp')
  case outcome of
    (EvaluationSuccess res, EvaluationSuccess res') -> res === res'
    _                                               -> failure

rotateHomogenous :: PropertyT IO ()
rotateHomogenous = do
  w8 <- forAllWith ppShow . Gen.element $ [zeroBits, complement zeroBits]
  cover 45 "all ones" $ w8 == complement zeroBits
  cover 45 "all zeroes" $ w8 == zeroBits
  len <- forAllWith ppShow . Gen.integral $ byteBoundRange
  let bs = BS.replicate len w8
  rotation <- forAllWith ppShow . Gen.integral $ indexRange
  let comp = mkIterApp () (builtin () RotateByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () rotation
        ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === mkConstant @ByteString () bs
    _                     -> failure

shiftHomogenous :: PropertyT IO ()
shiftHomogenous = do
  len <- forAllWith ppShow . Gen.integral $ byteBoundRange
  i <- forAllWith ppShow . Gen.integral $ indexRange
  let bs = BS.replicate len zeroBits
  let comp = mkIterApp () (builtin () ShiftByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () i
        ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === mkConstant @ByteString () bs
    _                     -> failure

rotateSum :: PropertyT IO ()
rotateSum = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  i <- forAllWith ppShow . Gen.integral $ indexRange
  j <- forAllWith ppShow . Gen.integral $ indexRange
  let comp1 = mkIterApp () (builtin () RotateByteString) [
        mkIterApp () (builtin () RotateByteString) [
          mkConstant @ByteString () bs,
          mkConstant @Integer () i
          ],
        mkConstant @Integer () j
        ]
  let comp2 = mkIterApp () (builtin () RotateByteString) [
        mkConstant @ByteString () bs,
        mkIterApp () (builtin () AddInteger) [
          mkConstant @Integer () i,
          mkConstant @Integer () j
          ]
        ]
  outcome <- bitraverse cekEval cekEval (comp1, comp2)
  case outcome of
    (EvaluationSuccess res, EvaluationSuccess res') -> res === res'
    _                                               -> failure

shiftSum :: PropertyT IO ()
shiftSum = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  ij <- forAllWith ppShow . Gen.integral $ indexRange
  (i, j) <- forAllWith ppShow . genSplit $ ij
  let comp1 = mkIterApp () (builtin () ShiftByteString) [
        mkIterApp () (builtin () ShiftByteString) [
          mkConstant @ByteString () bs,
          mkConstant @Integer () i
          ],
        mkConstant @Integer () j
        ]
  let comp2 = mkIterApp () (builtin () ShiftByteString) [
        mkConstant @ByteString () bs,
        mkConstant @Integer () ij
        ]
  outcome <- bitraverse cekEval cekEval (comp1, comp2)
  case outcome of
    (EvaluationSuccess res, EvaluationSuccess res') -> res === res'
    _                                               -> failure

iToBsRoundtrip :: PropertyT IO ()
iToBsRoundtrip = do
  i <- forAllWith ppShow . Gen.integral $ indexRange
  let comp = mkIterApp () (builtin () ByteStringToInteger) [
              mkIterApp () (builtin () IntegerToByteString) [
                mkConstant @Integer () i
                ]
              ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === mkConstant @Integer () i
    _                     -> failure

bsToITrailing :: PropertyT IO ()
bsToITrailing = do
  testCase <- forAllWith ppShow genBsToITrailingCase
  cover 45 "negative representation" . isNegativeCase $ testCase
  cover 45 "non-negative representation" . not . isNegativeCase $ testCase
  let (extension, bs) = getBsToITrailingArgs testCase
  let comp = mkIterApp () (builtin () ByteStringToInteger) [
              mkIterApp () (builtin () AppendByteString) [
                mkConstant @ByteString () extension,
                mkConstant @ByteString () bs
                ]
              ]
  let comp' = mkIterApp () (builtin () ByteStringToInteger) [
                mkConstant @ByteString () bs
                ]
  outcome <- bitraverse cekEval cekEval (comp, comp')
  case outcome of
    (EvaluationSuccess res, EvaluationSuccess res') -> res === res'
    _                                               -> failure

bsToIHomogenous :: PropertyT IO ()
bsToIHomogenous = do
  w8 <- forAllWith ppShow . Gen.element $ [zeroBits, complement zeroBits]
  len <- forAllWith ppShow . Gen.integral $ integerRange
  cover 45 "all zeroes" $ w8 == zeroBits
  cover 45 "all ones" $ w8 == complement zeroBits
  let bs = BS.replicate len w8
  let comp = mkIterApp () (builtin () ByteStringToInteger) [
              mkConstant @ByteString () bs
              ]
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res ->
      res === (mkConstant @Integer () $ if | len == 0       -> 0
                                           | w8 == zeroBits -> 0
                                           | otherwise      -> (-1))
    _ -> failure

-- Helpers

data BsToITrailingCase =
  BsToINonNegative ByteString ByteString |
  BsToINegative ByteString ByteString
  deriving stock (Eq, Show)

isNegativeCase :: BsToITrailingCase -> Bool
isNegativeCase = \case
  BsToINegative{} -> True
  _               -> False

getBsToITrailingArgs :: BsToITrailingCase -> (ByteString, ByteString)
getBsToITrailingArgs = \case
  BsToINegative bs bs'    -> (bs, bs')
  BsToINonNegative bs bs' -> (bs, bs')

data WriteBitAgreementCase =
  WriteBitReadSame Int Integer |
  WriteBitReadDifferent Int Integer Integer
  deriving stock (Eq, Show)

getWriteBitAgreementArgs :: WriteBitAgreementCase -> (ByteString, Integer, Integer)
getWriteBitAgreementArgs = \case
  WriteBitReadSame len ix          -> (BS.replicate len zeroBits, ix, ix)
  WriteBitReadDifferent len ix ix' -> (BS.replicate len zeroBits, ix, ix')

data FFSAppendType = ZeroBoth | ZeroSecond | NotZeroSecond
  deriving stock (Eq)

data FFSAppendCase =
  FFSAppendBothZero Int Int |
  FFSAppendSecondZero ByteString Int |
  FFSAppendSecondNonZero ByteString ByteString
  deriving stock (Eq, Show)

getFFSAppendArgs :: FFSAppendCase -> (ByteString, ByteString)
getFFSAppendArgs = \case
  FFSAppendBothZero len len'    -> (BS.replicate len zeroBits, BS.replicate len' zeroBits)
  FFSAppendSecondZero bs len    -> (bs, BS.replicate len zeroBits)
  FFSAppendSecondNonZero bs bs' -> (bs, bs')

ffsAppendType :: FFSAppendCase -> FFSAppendType
ffsAppendType = \case
  FFSAppendBothZero{}      -> ZeroBoth
  FFSAppendSecondZero{}    -> ZeroSecond
  FFSAppendSecondNonZero{} -> NotZeroSecond

data WriteBitCase =
  WriteBitOutOfBounds ByteString Integer Bool |
  WriteBitInBounds ByteString Integer Bool
  deriving stock (Eq, Show)

_WriteBitResult :: Fold WriteBitCase Bool
_WriteBitResult = folding $ \case
  WriteBitInBounds _ _ b -> pure b
  _                      -> Nothing

getWriteBitArgs :: WriteBitCase -> (ByteString, Integer, Bool)
getWriteBitArgs = \case
  WriteBitOutOfBounds bs ix b -> (bs, ix, b)
  WriteBitInBounds bs ix b    -> (bs, ix, b)

data BitAppendCase =
  AppendOutOfBounds ByteString ByteString Integer |
  AppendInBoundsFirst ByteString ByteString Integer |
  AppendInBoundsSecond ByteString ByteString Integer
  deriving stock (Eq, Show)

appendOutOfBounds :: BitAppendCase -> Bool
appendOutOfBounds = \case
  AppendOutOfBounds{} -> True
  _                   -> False

appendInBoundsFirst :: BitAppendCase -> Bool
appendInBoundsFirst = \case
  AppendInBoundsFirst{} -> True
  _                     -> False

appendInBoundsSecond :: BitAppendCase -> Bool
appendInBoundsSecond = \case
  AppendInBoundsSecond{} -> True
  _                      -> False

getBitAppendArgs :: BitAppendCase -> (ByteString, ByteString, Integer)
getBitAppendArgs = \case
  AppendOutOfBounds bs bs' ix    -> (bs, bs', ix)
  AppendInBoundsFirst bs bs' ix  -> (bs, bs', ix)
  AppendInBoundsSecond bs bs' ix -> (bs, bs', ix)

bitAt :: Word8 -> Integer -> Maybe Bool
bitAt w8 ix = do
  guard (ix >= 0)
  guard (ix < 8)
  let mask = bit 0 `shiftL` fromIntegral ix
  pure $ case mask .&. w8 of
    0 -> False
    _ -> True

demorgan ::
  DefaultFun ->
  DefaultFun ->
  PropertyT IO ()
demorgan b b' = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  let len = BS.length bs
  bs' <- forAllWith ppShow . Gen.bytes . Range.singleton $ len
  outcome <- demorganing b b' bs bs'
  case outcome of
    (EvaluationSuccess res1, EvaluationSuccess res2) -> res1 === res2
    _                                                -> failure

demorganing ::
  DefaultFun ->
  DefaultFun ->
  ByteString ->
  ByteString ->
  PropertyT IO (EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()),
                EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()))
demorganing fun fun' x y = do
  let x' = mkConstant @ByteString () x
  let y' = mkConstant @ByteString () y
  let comp = mkIterApp () (builtin () ComplementByteString) [
        mkIterApp () (builtin () fun) [x', y']
        ]
  let comp' = mkIterApp () (builtin () fun') [
        mkIterApp () (builtin () ComplementByteString) [x'],
        mkIterApp () (builtin () ComplementByteString) [y']
        ]
  bitraverse cekEval cekEval (comp, comp')

data AssociativeCase =
  AssociativeMismatched ByteString ByteString ByteString |
  AssociativeMatched ByteString ByteString ByteString ByteString
  deriving stock (Eq, Show)

getAssociativeArgs :: AssociativeCase -> (ByteString, ByteString, ByteString)
getAssociativeArgs = \case
  AssociativeMismatched x y z -> (x, y, z)
  AssociativeMatched x y z _  -> (x, y, z)

_AssociativeResult :: Fold AssociativeCase ByteString
_AssociativeResult = folding $ \case
  AssociativeMatched _ _ _ res -> pure res
  _                            -> Nothing

associative ::
  (Word8 -> Word8 -> Word8) ->
  DefaultFun ->
  PropertyT IO ()
associative f b = do
  testCase <- forAllWith ppShow . genAssociativeCase $ f
  cover 45 "mismatched lengths" . hasn't _AssociativeResult $ testCase
  cover 45 "matched lengths" . has _AssociativeResult $ testCase
  let expectedMay = preview _AssociativeResult testCase
  let (x, y, z) = getAssociativeArgs testCase
  outcome <- associatively b x y z
  case (outcome, expectedMay) of
    ((EvaluationFailure, EvaluationFailure), Nothing) -> success
    (_, Nothing) -> annotate "Unexpected failure" >> failure
    ((EvaluationSuccess leftAssoc, EvaluationSuccess rightAssoc), Just expected) -> do
      leftAssoc === rightAssoc
      leftAssoc === mkConstant () expected
    _ -> annotate "Unexpected failure" >> failure

associatively ::
  DefaultFun ->
  ByteString ->
  ByteString ->
  ByteString ->
  PropertyT IO (EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()),
                EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()))
associatively fun x y z = do
  let x' = mkConstant @ByteString () x
  let y' = mkConstant @ByteString () y
  let z' = mkConstant @ByteString () z
  let leftAssoc = mkIterApp () (builtin () fun) [
        mkIterApp () (builtin () fun) [x', y'],
        z'
        ]
  let rightAssoc = mkIterApp () (builtin () fun) [
        x',
        mkIterApp () (builtin () fun) [y', z']
        ]
  bitraverse cekEval cekEval (leftAssoc, rightAssoc)

self :: DefaultFun -> PropertyT IO ()
self b = do
  bs <- forAllWith ppShow . Gen.bytes $ byteBoundRange
  let bs' = mkConstant @ByteString () bs
  let comp = mkIterApp () (builtin () b) [bs', bs']
  outcome <- cekEval comp
  case outcome of
    EvaluationSuccess res -> res === mkConstant @ByteString () bs
    _                     -> failure

data AbsorbingCase =
  AbsorbingMismatched ByteString Int Word8 |
  AbsorbingMatched ByteString Word8
  deriving stock (Eq, Show)

_AbsorbingResult :: Fold AbsorbingCase ByteString
_AbsorbingResult = folding $ \case
  AbsorbingMatched bs w8 -> pure . BS.replicate (BS.length bs) $ w8
  _                      -> Nothing

getAbsorbingArgs :: AbsorbingCase -> (ByteString, ByteString)
getAbsorbingArgs = \case
  AbsorbingMismatched bs len w8 -> (bs, BS.replicate len w8)
  AbsorbingMatched bs w8        -> (bs, BS.replicate (BS.length bs) w8)

absorbing ::
  Word8 ->
  DefaultFun ->
  PropertyT IO ()
absorbing w8 b = do
  testCase <- forAllWith ppShow . genAbsorbingCase $ w8
  cover 45 "mismatched lengths" . hasn't _AbsorbingResult $ testCase
  cover 45 "matched lengths" . has _AbsorbingResult $ testCase
  let expectedMay = preview _AbsorbingResult testCase
  let (leftArg, rightArg) = getAbsorbingArgs testCase
  outcome <- commutatively b leftArg rightArg
  case (outcome, expectedMay) of
    ((EvaluationFailure, EvaluationFailure), Nothing) -> success
    (_, Nothing) -> do
      annotate "Unexpected success"
      failure
    ((EvaluationSuccess l2r, EvaluationSuccess r2l), Just expected) -> do
      l2r === r2l
      l2r === mkConstant () expected
    _ -> do
      annotate "Unexpected failure"
      failure

data IdentityCase =
  IdentityMismatched ByteString Int Word8 |
  IdentityMatched ByteString Word8
  deriving stock (Eq, Show)

_IdentityResult :: Fold IdentityCase ByteString
_IdentityResult = folding $ \case
  IdentityMatched res _ -> pure res
  _                     -> Nothing

getIdentityArgs :: IdentityCase -> (ByteString, ByteString)
getIdentityArgs = \case
  IdentityMismatched bs len w8 -> (bs, BS.replicate len w8)
  IdentityMatched bs w8        -> (bs, BS.replicate (BS.length bs) w8)

identity ::
  Word8 ->
  DefaultFun ->
  PropertyT IO ()
identity w8 b = do
  testCase <- forAllWith ppShow . genIdentityCase $ w8
  cover 45 "mismatched lengths" . hasn't _IdentityResult $ testCase
  cover 45 "matched lengths" . has _IdentityResult $ testCase
  let expectedMay = preview _IdentityResult testCase
  let (leftArg, rightArg) = getIdentityArgs testCase
  outcome <- commutatively b leftArg rightArg
  case (outcome, expectedMay) of
    ((EvaluationFailure, EvaluationFailure), Nothing) -> success
    (_, Nothing) -> do
      annotate "Unexpected success"
      failure
    ((EvaluationSuccess l2r, EvaluationSuccess r2l), Just expected) -> do
      l2r === r2l
      l2r === mkConstant () expected
    _ -> do
      annotate "Unexpected failure"
      failure

data CommutativeCase =
  MismatchedLengths ByteString ByteString |
  MatchedLengths ByteString ByteString ByteString
  deriving stock (Eq, Show)

getArgs :: CommutativeCase -> (ByteString, ByteString)
getArgs = \case
  MismatchedLengths bs bs' -> (bs, bs')
  MatchedLengths bs bs' _  -> (bs, bs')

_CommutativeResult :: Fold CommutativeCase ByteString
_CommutativeResult = folding $ \case
  MatchedLengths _ _ res -> pure res
  _                      -> Nothing

commutative ::
  (Word8 -> Word8 -> Word8) ->
  DefaultFun ->
  PropertyT IO ()
commutative f b = do
  testCase <- forAllWith ppShow . genCommutativeCase $ f
  cover 45 "mismatched lengths" . hasn't _CommutativeResult $ testCase
  cover 45 "matched lengths" . has _CommutativeResult $ testCase
  let expectedMay = preview _CommutativeResult testCase
  let (leftArg, rightArg) = getArgs testCase
  outcome <- commutatively b leftArg rightArg
  case (outcome, expectedMay) of
    ((EvaluationFailure, EvaluationFailure), Nothing) -> success
    (_, Nothing) -> do
      annotate "Unexpected success"
      failure
    ((EvaluationSuccess l2r, EvaluationSuccess r2l), Just expected) -> do
      l2r === r2l
      l2r === mkConstant () expected
    _ -> do
      annotate "Unexpected failure"
      failure

commutatively ::
  DefaultFun ->
  ByteString ->
  ByteString ->
  PropertyT IO (EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()),
                EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()))
commutatively fun leftArg rightArg = do
  let leftArg' = mkConstant @ByteString () leftArg
  let rightArg' = mkConstant @ByteString () rightArg
  let oneDirection = go leftArg' rightArg'
  let otherDirection = go rightArg' leftArg'
  bitraverse cekEval cekEval (oneDirection, otherDirection)
  where
    go :: Term Untyped.TyName Name DefaultUni DefaultFun () ->
          Term Untyped.TyName Name DefaultUni DefaultFun () ->
          Term Untyped.TyName Name DefaultUni DefaultFun ()
    go arg1 arg2 = mkIterApp () (builtin () fun) [arg1, arg2]

cekEval ::
  Term Untyped.TyName Name DefaultUni DefaultFun () ->
  PropertyT IO (EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()))
cekEval = fmap fst . evalEither . cekEval'

cekEval' ::
  Term Untyped.TyName Name DefaultUni DefaultFun () ->
  Either (Error DefaultUni DefaultFun ())
         (EvaluationResult (Untyped.Term Name DefaultUni DefaultFun ()), [Text])
cekEval' = typecheckEvaluateCek defaultCekParameters

-- Generators

genBsToITrailingCase :: Gen BsToITrailingCase
genBsToITrailingCase = Gen.choice [negative, nonNegative]
  where
    negative :: Gen BsToITrailingCase
    negative = do
      len <- Gen.integral byteBoundRange
      extLen <- Gen.integral byteBoundRange
      w8 <- Gen.element [129 :: Word8 .. 255]
      bs <- Gen.bytes . Range.singleton $ len
      pure .
        BsToINegative (BS.replicate extLen . complement $ zeroBits) .
        BS.cons w8 $ bs
    nonNegative :: Gen BsToITrailingCase
    nonNegative = do
      len <- Gen.integral byteBoundRange
      extLen <- Gen.integral byteBoundRange
      BsToINonNegative (BS.replicate extLen zeroBits) <$>
        case len of
          0 -> pure BS.empty
          _ -> Gen.choice [pure . powerOf2 $ len, notPowerOf2 len]
    powerOf2 :: Int -> ByteString
    powerOf2 len = BS.cons 128 . BS.replicate (len - 1) $ zeroBits
    notPowerOf2 :: Int -> Gen ByteString
    notPowerOf2 len =
      BS.cons <$> Gen.element [0 :: Word8 .. 127] <*>
                  (Gen.bytes . Range.singleton $ len - 1)

genWriteBitAgreementCase :: Gen WriteBitAgreementCase
genWriteBitAgreementCase = do
  len <- Gen.integral . Range.linear 1 $ 64
  Gen.choice [same len, different len]
  where
    same :: Int -> Gen WriteBitAgreementCase
    same len = do
      let bitLen = fromIntegral $ len * 8
      ix <- Gen.integral . indexRangeFor $ bitLen
      pure . WriteBitReadSame len $ ix
    different :: Int -> Gen WriteBitAgreementCase
    different len = do
      let bitLen = fromIntegral $ len * 8
      readIx <- Gen.integral . indexRangeFor $ bitLen
      writeIx <- Gen.filter (readIx /=) . Gen.integral . indexRangeFor $ bitLen
      pure . WriteBitReadDifferent len writeIx $ readIx

genCommutativeCase :: (Word8 -> Word8 -> Word8) -> Gen CommutativeCase
genCommutativeCase f = Gen.choice [mismatched, matched]
  where
    mismatched :: Gen CommutativeCase
    mismatched = do
      leftArg <- Gen.bytes byteBoundRange
      rightArg <- Gen.bytes byteBoundRange
      if BS.length leftArg /= BS.length rightArg
      then pure . MismatchedLengths leftArg $ rightArg
      else do
        let diff = BS.length leftArg - BS.length rightArg
        extension <- Gen.bytes . diffRange $ diff
        let leftArg' = leftArg <> extension
        Gen.element [MismatchedLengths leftArg' rightArg,
                     MismatchedLengths rightArg leftArg']
    matched :: Gen CommutativeCase
    matched = do
      leftArg <- Gen.bytes byteBoundRange
      let len = BS.length leftArg
      rightArg <- Gen.bytes . Range.singleton $ len
      let result = fromListN len . BS.zipWith f leftArg $ rightArg
      pure . MatchedLengths leftArg rightArg $ result

genIdentityCase :: Word8 -> Gen IdentityCase
genIdentityCase w8 = Gen.choice [mismatched, matched]
  where
    mismatched :: Gen IdentityCase
    mismatched = do
      bs <- Gen.bytes byteBoundRange
      let len = BS.length bs
      genLen <- Gen.filter (/= len) . Gen.int $ byteBoundRange
      pure . IdentityMismatched bs genLen $ w8
    matched :: Gen IdentityCase
    matched = do
      bs <- Gen.bytes byteBoundRange
      pure . IdentityMatched bs $ w8

genAbsorbingCase :: Word8 -> Gen AbsorbingCase
genAbsorbingCase w8 = Gen.choice [mismatched, matched]
  where
    mismatched :: Gen AbsorbingCase
    mismatched = do
      bs <- Gen.bytes byteBoundRange
      let len = BS.length bs
      genLen <- Gen.filter (/= len) . Gen.int $ byteBoundRange
      pure . AbsorbingMismatched bs genLen $ w8
    matched :: Gen AbsorbingCase
    matched = do
      bs <- Gen.bytes byteBoundRange
      pure . AbsorbingMatched bs $ w8

genAssociativeCase :: (Word8 -> Word8 -> Word8) -> Gen AssociativeCase
genAssociativeCase f = Gen.choice [mismatched, matched]
  where
    mismatched :: Gen AssociativeCase
    mismatched = do
      x <- Gen.bytes byteBoundRange
      y <- Gen.bytes byteBoundRange
      z <- Gen.bytes byteBoundRange
      if BS.length x == BS.length y && BS.length y == BS.length z
      then do
        extension <- Gen.bytes . diffRange $ 5
        let x' = x <> extension
        Gen.element [AssociativeMismatched x' y z,
                     AssociativeMismatched y x' z,
                     AssociativeMismatched y z x']
      else pure . AssociativeMismatched x y $ z
    matched :: Gen AssociativeCase
    matched = do
      x <- Gen.bytes byteBoundRange
      let len = BS.length x
      y <- Gen.bytes . Range.singleton $ len
      z <- Gen.bytes . Range.singleton $ len
      let result = fromListN len . zipWith f (toList x) . BS.zipWith f y $ z
      pure . AssociativeMatched x y z $ result

genBitAppendCase :: Gen BitAppendCase
genBitAppendCase = Gen.choice [oob, inBounds1, inBounds2]
  where
    oob :: Gen BitAppendCase
    oob = do
      bs <- Gen.bytes byteBoundRange
      bs' <- Gen.bytes byteBoundRange
      let len = fromIntegral $ 8 * (BS.length bs + BS.length bs')
      ix <- Gen.choice [tooLowIx len, tooHighIx len]
      pure . AppendOutOfBounds bs bs' $ ix
    inBounds1 :: Gen BitAppendCase
    inBounds1 = do
      bs <- Gen.bytes byteBoundRange
      w8 <- Gen.enumBounded
      let firstArg = BS.cons w8 bs
      bs' <- Gen.bytes byteBoundRange
      let len = fromIntegral $ 8 * BS.length firstArg
      let len' = fromIntegral $ 8 * BS.length bs'
      ix <- (len' +) <$> (Gen.integral . indexRangeFor $ len)
      pure . AppendInBoundsFirst firstArg bs' $ ix
    inBounds2 :: Gen BitAppendCase
    inBounds2 = do
      bs <- Gen.bytes byteBoundRange
      bs' <- Gen.bytes byteBoundRange
      w8 <- Gen.enumBounded
      let secondArg = BS.cons w8 bs'
      let len' = fromIntegral $ 8 * BS.length secondArg
      ix <- Gen.integral . indexRangeFor $ len'
      pure . AppendInBoundsSecond bs secondArg $ ix

genWriteBitCase :: Gen WriteBitCase
genWriteBitCase = Gen.choice [oob, inBounds]
  where
    oob :: Gen WriteBitCase
    oob = do
      bs <- Gen.bytes byteBoundRange
      let len = fromIntegral $ 8 * BS.length bs
      b <- Gen.enumBounded
      ix <- Gen.choice [tooLowIx len, tooHighIx len]
      pure . WriteBitOutOfBounds bs ix $ b
    inBounds :: Gen WriteBitCase
    inBounds = do
      bs <- Gen.bytes byteBoundRange
      w8 <- Gen.enumBounded
      let bs' = BS.cons w8 bs
      let len = fromIntegral $ 8 * BS.length bs'
      b <- Gen.enumBounded
      ix <- Gen.integral . indexRangeFor $ len
      pure . WriteBitInBounds bs' ix $ b

genFFSAppendCase :: Gen FFSAppendCase
genFFSAppendCase = Gen.choice [allZero, secondZero, secondNonZero]
  where
    allZero :: Gen FFSAppendCase
    allZero = do
      len <- Gen.integral . Range.linear 0 $ 63
      len' <- Gen.integral . Range.linear 0 $ 63
      pure . FFSAppendBothZero len $ len'
    secondZero :: Gen FFSAppendCase
    secondZero = do
      bs <- Gen.bytes byteBoundRange
      w8 <- Gen.filter (/= zeroBits) Gen.enumBounded
      let firstArg = BS.cons w8 bs
      len' <- Gen.integral . Range.linear 0 $ 63
      pure . FFSAppendSecondZero firstArg $ len'
    secondNonZero :: Gen FFSAppendCase
    secondNonZero = do
      bs <- Gen.bytes byteBoundRange
      w8 <- Gen.filter (/= zeroBits) Gen.enumBounded
      bs' <- Gen.bytes byteBoundRange
      w8' <- Gen.filter (/= zeroBits) Gen.enumBounded
      pure . FFSAppendSecondNonZero (BS.cons w8 bs) . BS.cons w8' $ bs'

tooLowIx :: Integer -> Gen Integer
tooLowIx = Gen.integral . Range.linear (-1) . negate

tooHighIx :: Integer -> Gen Integer
tooHighIx i = Gen.integral . Range.linear i $ i * 2

genSplit :: Integer -> Gen (Integer, Integer)
genSplit ij = Gen.element $ case signum ij of
  1 -> [(i, j) | i <- [0 .. ij], j <- [0 .. ij], i + j == ij]
  0 -> [(0, 0)]
  _ -> [(i, j) | i <- [0, (-1) .. ij], j <- [0, (-1) .. ij], i + j == ij]

-- Ranges

byteBoundRange :: Range Int
byteBoundRange = Range.linear 0 64

diffRange :: Int -> Range Int
diffRange diff = let param = abs diff + 1 in
  Range.linear param (param * 2)

indexRange :: Range Integer
indexRange = Range.linearFrom 0 (-100) 100

indexRangeOf :: Integer -> Range Integer
indexRangeOf lim = Range.constantFrom 0 (negate lim) (lim - 1)

indexRangeFor :: Integer -> Range Integer
indexRangeFor i = Range.constant 0 (i - 1)

integerRange :: Range Int
integerRange = Range.linear 0 8
