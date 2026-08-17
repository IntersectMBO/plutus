{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Canonical runtime encoding for 'MatchDataConstr' pattern tables.
module PlutusCore.Default.MatchDataConstr.Encoding
  ( MatchDataConstrPattern (..)
  , decodeMatchDataConstrTable
  , encodeMatchDataConstrTable
  , matchDataConstrPatternCaptureCount
  , mkMatchDataConstrPattern
  ) where

import PlutusPrelude

import Control.Monad (unless, when)
import Data.Bits (shiftL, shiftR, testBit, (.&.), (.|.))
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as BSL
import Data.Text (Text)
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector

{-| The exact constructor arity and one selector byte per constructor field.

A selector is @1@ when the corresponding field is captured and @0@ when it is skipped. Requiring
exactly one canonical byte per field makes the encoded pattern length equal to the constructor
arity. -}
data MatchDataConstrPattern = MatchDataConstrPattern
  { matchDataConstrPatternArity :: !Int
  , matchDataConstrPatternSelectors :: !BS.ByteString
  }
  deriving stock (Eq, Show)

{-| Build the canonical field-selector encoding used by the matcher.

For example, arity 6 with captures at fields 0 and 5 is encoded as @[1,0,0,0,0,1]@. -}
mkMatchDataConstrPattern :: Int -> [Int] -> Either Text MatchDataConstrPattern
mkMatchDataConstrPattern arity captureIndices
  | arity < 0 = Left "matchDataConstr pattern arity must be non-negative"
  | not $ and $ zipWith (<) captureIndices (drop 1 captureIndices) =
      Left "matchDataConstr capture indices must be strictly increasing"
  | any (\index -> index < 0 || index >= arity) captureIndices =
      Left "matchDataConstr capture index is outside the constructor arity"
  | otherwise = pure . MatchDataConstrPattern arity . BS.pack $ selectors 0 captureIndices
  where
    selectors !field captures
      | field == arity = []
      | otherwise = case captures of
          capture : rest
            | capture == field -> 1 : selectors (field + 1) rest
          _ -> 0 : selectors (field + 1) captures

matchDataConstrPatternCaptureCount :: MatchDataConstrPattern -> Int
matchDataConstrPatternCaptureCount (MatchDataConstrPattern _ selectors) =
  BS.count 1 selectors

{-| Encode a non-empty, tag-sorted pattern table.

The format is:

@entry-count, (constructor-tag, pattern-byte-length, field-selectors)*@

The three structural numbers use canonical unsigned LEB128. There is deliberately no version
field: changing this builtin's format requires a new builtin or language version, not an in-band
byte that every script must carry and every call must inspect. -}
encodeMatchDataConstrTable
  :: Vector (Integer, MatchDataConstrPattern)
  -> Either Text BS.ByteString
encodeMatchDataConstrTable entries = do
  when (Vector.null entries) $ Left "matchDataConstr requires a non-empty pattern table"
  let tags = fst <$> Vector.toList entries
  unless (and $ zipWith (<) tags $ drop 1 tags) $
    Left "matchDataConstr constructor tags must be strictly increasing"
  when (any (\tag -> tag < 0 || tag > toInteger (maxBound :: Word64)) tags) $
    Left "matchDataConstr constructor tags must fit in a Word64"
  traverse_ (validatePattern . snd) entries
  pure . BSL.toStrict . Builder.toLazyByteString $
    encodeNatural (toInteger $ Vector.length entries)
      <> foldMap encodeEntry entries
  where
    encodeEntry (tag, MatchDataConstrPattern _ selectors) =
      encodeNatural tag
        <> encodeNatural (toInteger $ BS.length selectors)
        <> Builder.byteString selectors

decodeMatchDataConstrTable
  :: BS.ByteString
  -> Either Text (Vector (Integer, MatchDataConstrPattern))
decodeMatchDataConstrTable bytes = do
  when (BS.null bytes) $ Left "matchDataConstr representation is empty"
  (entryCountInteger, afterCount) <-
    decodeNatural "entry count" (toInteger $ BS.length bytes) bytes 0
  when (entryCountInteger == 0) $ Left "matchDataConstr requires a non-empty pattern table"
  when (entryCountInteger > toInteger (BS.length bytes - afterCount)) $
    Left "matchDataConstr entry count exceeds the representation size"
  (entries, finalOffset) <- go (fromInteger entryCountInteger) afterCount Nothing []
  unless (finalOffset == BS.length bytes) $
    Left "matchDataConstr representation has trailing bytes"
  pure . Vector.fromList $ reverse entries
  where
    go !remaining !offset !previousTag !entries
      | remaining == (0 :: Int) = pure (entries, offset)
      | otherwise = do
          (tag, afterTag) <-
            decodeNatural "constructor tag" (toInteger (maxBound :: Word64)) bytes offset
          when (maybe False (>= tag) previousTag) $
            Left "matchDataConstr constructor tags must be strictly increasing"
          (byteCountInteger, afterByteCount) <-
            decodeNatural "pattern byte length" (toInteger $ BS.length bytes) bytes afterTag
          let !remainingBytes = BS.length bytes - afterByteCount
          when (byteCountInteger > toInteger remainingBytes) $
            Left "matchDataConstr capture pattern is truncated"
          let !byteCount = fromInteger byteCountInteger
              !endOffset = afterByteCount + byteCount
              !selectors = BS.take byteCount $ BS.drop afterByteCount bytes
          pattern <- decodePattern selectors
          go (remaining - 1) endOffset (Just tag) ((tag, pattern) : entries)

validatePattern :: MatchDataConstrPattern -> Either Text ()
validatePattern (MatchDataConstrPattern expectedArity selectors) = do
  MatchDataConstrPattern decodedArity _ <- decodePattern selectors
  unless (decodedArity == expectedArity) $
    Left "matchDataConstr capture pattern does not encode its declared arity"

decodePattern :: BS.ByteString -> Either Text MatchDataConstrPattern
decodePattern selectors = do
  unless (BS.all (\selector -> selector == 0 || selector == 1) selectors) $
    Left "matchDataConstr field selector must be zero or one"
  pure $ MatchDataConstrPattern (BS.length selectors) selectors

encodeNatural :: Integer -> Builder.Builder
encodeNatural natural
  | natural < 0 = error "encodeNatural: negative input"
  | otherwise = go natural
  where
    go !value =
      let !payload = fromIntegral (value .&. 0x7f)
          !rest = value `shiftR` 7
       in if rest == 0
            then Builder.word8 payload
            else Builder.word8 (payload .|. 0x80) <> go rest

decodeNatural
  :: Text
  -> Integer
  -> BS.ByteString
  -> Int
  -> Either Text (Integer, Int)
decodeNatural label upperBound bytes = go (0 :: Int) 0 (0 :: Int)
  where
    go !shift !accumulator !groups !offset
      | offset >= BS.length bytes = Left $ "truncated matchDataConstr " <> label
      | otherwise =
          let !byte = BS.index bytes offset
              !payload = byte .&. 0x7f
              !accumulator' = accumulator .|. (toInteger payload `shiftL` shift)
           in if accumulator' > upperBound
                then Left $ "matchDataConstr " <> label <> " is too large"
                else
                  if testBit byte 7
                    then go (shift + 7) accumulator' (groups + 1) (offset + 1)
                    else
                      if groups > 0 && payload == 0
                        then Left $ "non-canonical matchDataConstr " <> label
                        else pure (accumulator', offset + 1)
