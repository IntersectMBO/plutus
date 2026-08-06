{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-| Shallow matching on 'Data.Constr' for the 'MatchData' builtin.

The pattern table is represented statically by a closed 'TySOP'. Alternative @n@ describes the
fields of @Data.Constr n@: 'Data' marks a captured field and 'Unit' marks a skipped field. Before
erasure the table is reified to an array of capture masks. At runtime the builtin returns a
constructor with the same index and only the captured 'Data' fields. -}
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
        pure . someValue . Strict.fromList $
          fmap (BS.pack . fmap (\capture -> if capture then 1 else 0)) captureMasks
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
  captureMask <-
    maybe (fail "No matchData constructor corresponds to the Data.Constr tag") pure $
      encodedPatterns Strict.!? tagIndex
  let fieldCount = BS.length captureMask
      go !index []
        | index == fieldCount = Just []
        | otherwise = Nothing
      go !index (field : remainingFields)
        | index == fieldCount = Nothing
        | BSU.unsafeIndex captureMask index /= 0 =
            (fromValue field :) <$> go (index + 1) remainingFields
        | otherwise = go (index + 1) remainingFields
  captures <-
    maybe
      (fail "matchData payload length does not match the statically declared pattern arity")
      pure
      $ go 0 fields
  pure . OpaqueVConstr $
    fromConstr () (fromIntegral tagIndex) captures
matchData _ _ = fail "matchData only supports Data.Constr"
{-# INLINE matchData #-}
