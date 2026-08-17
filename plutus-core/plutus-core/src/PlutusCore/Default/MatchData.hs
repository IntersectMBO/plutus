{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-| Shallow matching on 'Data.Constr' for the 'MatchData' builtin.

The pattern table is an explicit, checked @BuiltinRep MatchData@ witness containing a sorted array
of constructor tags paired with distances between captures. Its static result index is the SOP of
captured 'Data' fields. Erasure retains the array as an ordinary constant and discards only the
index. At runtime the builtin returns a constructor whose local index is the position of the
matched entry and whose fields are only the captured 'Data' values. A @255@ byte continues the
same distance, and the final distance checks the exact constructor arity. -}
module PlutusCore.Default.MatchData
  ( MatchDataRepValue (..)
  , matchData
  , matchDataRepresentation
  , mkMatchDataRepType
  ) where

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Data (Data)
import PlutusCore.Data qualified as Data
import PlutusCore.Default.Universe
import PlutusCore.Evaluation.Machine.ExMemoryUsage
  ( ExMemoryUsage (..)
  , MatchDataCostedPatterns (..)
  )
import PlutusCore.Name.Unique (TyName)

import Control.Monad (unless, when)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BSU
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import Data.Vector.Strict qualified as Strict

{-| The Haskell-side runtime representation of @MatchDataRep result@. The @result@ parameter is
only used while deriving the PLC type scheme; at runtime the value is the existing encoded pattern
table. -}
newtype MatchDataRepValue val result = MatchDataRepValue
  { unMatchDataRepValue :: MatchDataCostedPatterns
  }

type instance UniOf (MatchDataRepValue val result) = UniOf val

instance ExMemoryUsage (MatchDataRepValue val result) where
  memoryUsage = memoryUsage . unMatchDataRepValue

-- | The abstract, result-indexed @MatchDataRep@ family.
mkMatchDataRepType
  :: ann
  -> Type TyName DefaultUni ann
  -> Type TyName DefaultUni ann
mkMatchDataRepType ann =
  TyApp ann $ TyBuiltin ann $ SomeTypeIn DefaultUniProtoMatchDataRep

instance
  (tyname ~ TyName, uni ~ DefaultUni, KnownTypeAst tyname uni result)
  => KnownTypeAst tyname uni (MatchDataRepValue val result)
  where
  type IsBuiltin _ (MatchDataRepValue val result) = 'False
  type ToHoles _ hole (MatchDataRepValue val result) = '[RunHole hole result]
  type ToBinds uni acc (MatchDataRepValue val result) = ToBinds uni acc result
  typeAst = mkMatchDataRepType () $ toTypeAst $ Proxy @result

instance
  (uni ~ UniOf val, ReadKnownIn uni val MatchDataCostedPatterns)
  => ReadKnownIn uni val (MatchDataRepValue val result)
  where
  readKnown = fmap MatchDataRepValue . readKnown
  {-# INLINE readKnown #-}

instance
  (uni ~ UniOf val, MakeKnownIn uni val MatchDataCostedPatterns)
  => MakeKnownIn uni val (MatchDataRepValue val result)
  where
  makeKnown = makeKnown . unMatchDataRepValue
  {-# INLINE makeKnown #-}

decodePatternCaptures :: BS.ByteString -> Either Text Int
decodePatternCaptures bytes
  | BS.null bytes = Left "matchData capture pattern must not be empty"
  | BS.last bytes == 255 = Left "matchData capture pattern ends in a continuation byte"
  | otherwise = Right $ BS.length (BS.filter (/= 255) bytes) - 1

decodePatternConstant
  :: Some (ValueOf DefaultUni)
  -> Either Text (Strict.Vector (Integer, BS.ByteString))
decodePatternConstant (Some (ValueOf uni value)) = case uni of
  DefaultUniArray (DefaultUniPair DefaultUniInteger DefaultUniByteString) -> Right value
  _ -> Left "matchData representation must contain an array of (integer, bytestring) pairs"

inferRepresentationType
  :: Some (ValueOf DefaultUni)
  -> Either Text (Type TyName DefaultUni ())
inferRepresentationType constant = do
  patterns <- decodePatternConstant constant
  when (Strict.null patterns) $
    Left "matchData requires a non-empty pattern table"
  let tags = fst <$> Strict.toList patterns
  unless (and $ zipWith (<) tags (drop 1 tags)) $
    Left "matchData constructor tags must be strictly increasing"
  captureCounts <- traverse (decodePatternCaptures . snd) $ Strict.toList patterns
  let dataTy = mkTyBuiltin @_ @Data ()
      resultTy = TySOP () $ fmap (`replicate` dataTy) captureCounts
  pure $ mkMatchDataRepType () resultTy

-- | Checked introduction metadata for explicit MatchData runtime representations.
matchDataRepresentation :: BuiltinRepresentation DefaultUni
matchDataRepresentation = BuiltinRepresentation inferRepresentationType

lookupPattern
  :: Integer
  -> Strict.Vector (Integer, BS.ByteString)
  -> Maybe (Int, BS.ByteString)
lookupPattern target patterns = go 0 $ Strict.length patterns
  where
    go !lower !upper
      | lower >= upper = Nothing
      | otherwise =
          let middle = lower + (upper - lower) `div` 2
              (candidateTag, patternBytes) = Strict.unsafeIndex patterns middle
           in case compare target candidateTag of
                LT -> go lower middle
                EQ -> Just (middle, patternBytes)
                GT -> go (middle + 1) upper
{-# INLINE lookupPattern #-}

-- | Match a 'Data.Constr' tag to the same SOP branch and capture its fields directly.
matchData
  :: forall val result
   . (HasConstantIn DefaultUni val, HasConstr val ())
  => MatchDataRepValue val result
  -> Data
  -> BuiltinResult (Opaque val result)
matchData (MatchDataRepValue (MatchDataCostedPatterns encodedPatterns)) (Data.Constr tag fields) = do
  (localIndex, capturePattern) <-
    maybe (fail "No matchData constructor corresponds to the Data.Constr tag") pure $
      lookupPattern tag encodedPatterns
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
  pure . Opaque $
    fromConstr () (fromIntegral localIndex) captures
matchData _ _ = fail "matchData only supports Data.Constr"
{-# INLINE matchData #-}
