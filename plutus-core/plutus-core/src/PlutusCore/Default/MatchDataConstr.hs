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

{-| Shallow matching on 'Data.Constr' for the 'MatchDataConstr' builtin.

The pattern table is an explicit, checked @BuiltinRep MatchDataConstr@ witness containing a canonical
'ByteString'. Its static result index is the SOP of captured 'Data' fields. Erasure retains the
bytes as an ordinary UPLC constant and discards only the index. At runtime the builtin returns a
constructor whose local index is the position of the matched entry and whose fields are only the
captured 'Data' values. Capture patterns contain one @0@ or @1@ selector byte per constructor
field, so their length also checks the exact constructor arity. -}
module PlutusCore.Default.MatchDataConstr
  ( MatchDataConstrRepValue (..)
  , module Encoding
  , matchDataConstr
  , matchDataConstrRepresentation
  , mkMatchDataConstrRepType
  ) where

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Data (Data)
import PlutusCore.Data qualified as Data
import PlutusCore.Default.MatchDataConstr.Encoding as Encoding
import PlutusCore.Default.Universe
import PlutusCore.Evaluation.Machine.ExMemoryUsage (ExMemoryUsage (..))
import PlutusCore.Name.Unique (TyName)

import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BSU
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Vector.Strict qualified as Strict

{-| The Haskell-side runtime representation of @MatchDataConstrRep result@. The @result@ parameter is
only used while deriving the PLC type scheme; at runtime the value is an ordinary 'ByteString'. -}
newtype MatchDataConstrRepValue val result = MatchDataConstrRepValue
  { unMatchDataConstrRepValue :: BS.ByteString
  }

type instance UniOf (MatchDataConstrRepValue val result) = UniOf val

instance ExMemoryUsage (MatchDataConstrRepValue val result) where
  memoryUsage = memoryUsage . unMatchDataConstrRepValue

-- | The abstract, result-indexed @MatchDataConstrRep@ family.
mkMatchDataConstrRepType
  :: ann
  -> Type TyName DefaultUni ann
  -> Type TyName DefaultUni ann
mkMatchDataConstrRepType ann =
  TyBuiltinRep ann (BuiltinRepName "matchDataConstr")

instance
  (tyname ~ TyName, uni ~ DefaultUni, KnownTypeAst tyname uni result)
  => KnownTypeAst tyname uni (MatchDataConstrRepValue val result)
  where
  type IsBuiltin _ (MatchDataConstrRepValue val result) = 'False
  type ToHoles _ hole (MatchDataConstrRepValue val result) = '[RunHole hole result]
  type ToBinds uni acc (MatchDataConstrRepValue val result) = ToBinds uni acc result
  typeAst = mkMatchDataConstrRepType () $ toTypeAst $ Proxy @result

instance
  (uni ~ UniOf val, ReadKnownIn uni val BS.ByteString)
  => ReadKnownIn uni val (MatchDataConstrRepValue val result)
  where
  readKnown = fmap MatchDataConstrRepValue . readKnown
  {-# INLINE readKnown #-}

instance
  (uni ~ UniOf val, MakeKnownIn uni val BS.ByteString)
  => MakeKnownIn uni val (MatchDataConstrRepValue val result)
  where
  makeKnown = makeKnown . unMatchDataConstrRepValue
  {-# INLINE makeKnown #-}

decodePatternConstant
  :: Some (ValueOf DefaultUni)
  -> Either Text BS.ByteString
decodePatternConstant (Some (ValueOf uni value)) = case uni of
  DefaultUniByteString -> Right value
  _ -> Left "matchDataConstr representation must contain a bytestring"

inferRepresentationType
  :: Some (ValueOf DefaultUni)
  -> Either Text (Type TyName DefaultUni ())
inferRepresentationType constant = do
  encodedPatterns <- decodePatternConstant constant
  patterns <- decodeMatchDataConstrTable encodedPatterns
  let captureCounts = matchDataConstrPatternCaptureCount . snd <$> Strict.toList patterns
  let dataTy = mkTyBuiltin @_ @Data ()
      resultTy = TySOP () $ fmap (`replicate` dataTy) captureCounts
  pure $ mkMatchDataConstrRepType () resultTy

-- | Checked introduction metadata for explicit MatchDataConstr runtime representations.
matchDataConstrRepresentation :: BuiltinRepresentation DefaultUni
matchDataConstrRepresentation = BuiltinRepresentation inferRepresentationType

lookupPattern
  :: Integer
  -> Strict.Vector (Integer, MatchDataConstrPattern)
  -> Maybe (Int, MatchDataConstrPattern)
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
matchDataConstr
  :: forall val result
   . (HasConstantIn DefaultUni val, HasConstr val ())
  => MatchDataConstrRepValue val result
  -> Data
  -> BuiltinResult (Opaque val result)
matchDataConstr (MatchDataConstrRepValue representationBytes) (Data.Constr tag fields) = do
  encodedPatterns <- either (fail . Text.unpack) pure $ decodeMatchDataConstrTable representationBytes
  (localIndex, capturePattern) <-
    maybe (fail "No matchDataConstr constructor corresponds to the Data.Constr tag") pure $
      lookupPattern tag encodedPatterns
  let fieldSelectors = matchDataConstrPatternSelectors capturePattern
      fieldCount = BS.length fieldSelectors
      go :: Int -> [Data] -> Maybe [val]
      go !index []
        | index == fieldCount = Just []
        | otherwise = Nothing
      go !index (field : rest)
        | index == fieldCount = Nothing
        | BSU.unsafeIndex fieldSelectors index == 1 =
            (fromValue field :) <$> go (index + 1) rest
        | otherwise = go (index + 1) rest
  captures <-
    maybe
      (fail "matchDataConstr payload length does not match the statically declared pattern arity")
      pure
      $ go 0 fields
  pure . Opaque $
    fromConstr () (fromIntegral localIndex) captures
matchDataConstr _ _ = fail "matchDataConstr only supports Data.Constr"
{-# INLINE matchDataConstr #-}
