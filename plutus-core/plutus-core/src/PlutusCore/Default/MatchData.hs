{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-| Shallow matching on 'Data.Constr' for the 'MatchData' builtin.

The pattern table is represented statically by a closed 'TySOP'. Alternative @n@ describes the
fields of @Data.Constr n@: 'Data' marks a captured field and 'Unit' marks a skipped field. Before
erasure the table is reified to an array of distances between captures. At runtime the builtin
returns a constructor with the same index and only the captured 'Data' fields. A @255@ byte
continues the same distance, and the final distance checks the exact constructor arity. -}
module PlutusCore.Default.MatchData
  ( matchData
  , matchDataTypeApplication
  ) where

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Data (Data)
import PlutusCore.Data qualified as Data
import PlutusCore.Default.Universe

import Data.Bits (toIntegralSized)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BSU
import Data.Text (Text)
import Data.Vector.Strict qualified as Strict

decodePatternTableType
  :: Type tyname DefaultUni ann
  -> Either Text [[Bool]]
decodePatternTableType = \case
  TySOP _ [] -> Left "matchData requires a non-empty pattern table"
  TySOP _ products ->
    traverse
      ( \productTy ->
          traverse
            ( \case
                TyBuiltin _ (SomeTypeIn DefaultUniUnit) -> Right False
                TyBuiltin _ (SomeTypeIn DefaultUniData) -> Right True
                _ -> Left "matchData constructor fields must have type Unit or Data"
            )
            productTy
      )
      products
  _ -> Left "matchData requires a sum-of-products type argument"

-- | Type-application metadata used to validate and reify the closed pattern table.
matchDataTypeApplication :: BuiltinTypeApplication DefaultUni
matchDataTypeApplication =
  BuiltinTypeApplication
    { btaInferType = \tableTy -> do
        captureMasks <- decodePatternTableType tableTy
        let dataTy = mkTyBuiltin @_ @Data ()
            captureTy =
              TySOP () $
                fmap (\mask -> dataTy <$ filter id mask) captureMasks
        pure $ TyFun () dataTy captureTy
    , btaReifyArgument = \tableTy -> do
        captureMasks <- decodePatternTableType tableTy
        let encodeGap gap
              | gap < 255 = [fromIntegral gap]
              | otherwise = 255 : encodeGap (gap - 255)
            encodePattern mask =
              let captureIndices = [index | (index, True) <- zip [0 ..] mask]
                  gaps =
                    zipWith
                      (\next previous -> next - previous - 1)
                      (captureIndices <> [length mask])
                      (-1 : captureIndices)
               in BS.pack $ concatMap encodeGap gaps
        pure . someValue . Strict.fromList $
          fmap encodePattern captureMasks
    }

-- | Match a 'Data.Constr' tag to the same SOP branch and capture its fields directly.
matchData
  :: forall val
   . (HasConstantIn DefaultUni val, HasConstr val ())
  => Strict.Vector ByteString
  -> Data
  -> BuiltinResult (OpaqueVConstr val)
matchData encodedPatterns (Data.Constr tag fields) = do
  tagIndex <-
    maybe (fail "No matchData constructor corresponds to the Data.Constr tag") pure $
      toIntegralSized tag
  capturePattern <-
    maybe (fail "No matchData constructor corresponds to the Data.Constr tag") pure $
      encodedPatterns Strict.!? tagIndex
  let patternSize = BS.length capturePattern
      go :: Int -> [Data] -> Maybe [val]
      go !offset remainingFields
        | offset == patternSize = Nothing
        | byte == 255 = skipMore (offset + 1) 255 remainingFields
        | otherwise = skipFinal (offset + 1) (fromIntegral byte) remainingFields
        where
          byte = BSU.unsafeIndex capturePattern offset
      skipMore :: Int -> Int -> [Data] -> Maybe [val]
      skipMore !nextOffset !count remainingFields
        | count == 0 = go nextOffset remainingFields
        | otherwise = case remainingFields of
            _ : rest -> skipMore nextOffset (count - 1) rest
            [] -> Nothing
      skipFinal :: Int -> Int -> [Data] -> Maybe [val]
      skipFinal !nextOffset !count remainingFields
        | count == 0 =
            if nextOffset == patternSize
              then case remainingFields of
                [] -> Just []
                _ -> Nothing
              else case remainingFields of
                field : rest -> (fromValue field :) <$> go nextOffset rest
                [] -> Nothing
        | otherwise = case remainingFields of
            _ : rest -> skipFinal nextOffset (count - 1) rest
            [] -> Nothing
  captures <-
    maybe
      (fail "matchData payload length does not match the statically declared pattern arity")
      pure
      $ go 0 fields
  pure . OpaqueVConstr $
    fromConstr () (fromIntegral tagIndex) captures
matchData _ _ = fail "matchData only supports Data.Constr"
{-# INLINE matchData #-}
