{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-| Shallow matching on 'Data.Constr' for the 'MatchData' builtin.

The pattern table is represented statically by a closed 'TySOP'. Alternative @n@ describes the
fields of @Data.Constr n@, and every field must have type 'Data'. Before erasure the table is
reified to the list of constructor arities. At runtime the builtin returns a constructor with the
same index and the original 'Data' fields as its captures. -}
module PlutusCore.Default.MatchData
  ( matchData
  , matchDataTypeApplication
  ) where

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Data (Data)
import PlutusCore.Data qualified as Data
import PlutusCore.Default.Universe

import Control.Monad (unless)
import Data.Text (Text)

decodePatternTableType
  :: Type tyname DefaultUni ann
  -> Either Text [Int]
decodePatternTableType = \case
  TySOP _ [] -> Left "matchData requires a non-empty pattern table"
  TySOP _ products ->
    traverse
      ( \productTy ->
          if all
            ( \case
                TyBuiltin _ (SomeTypeIn DefaultUniData) -> True
                _ -> False
            )
            productTy
            then Right $ length productTy
            else Left "matchData constructor fields must all have type Data"
      )
      products
  _ -> Left "matchData requires a sum-of-products type argument"

-- | Type-application metadata used to validate and reify the closed pattern table.
matchDataTypeApplication :: BuiltinTypeApplication DefaultUni
matchDataTypeApplication =
  BuiltinTypeApplication
    { btaInferType = \tableTy -> do
        _ <- decodePatternTableType tableTy
        pure $ TyFun () (mkTyBuiltin @_ @Data ()) tableTy
    , btaReifyArgument = \tableTy -> do
        arities <- decodePatternTableType tableTy
        pure . someValue $ fmap toInteger arities
    }

-- | Match a 'Data.Constr' tag to the same SOP branch and capture its fields directly.
matchData
  :: forall val
   . (HasConstantIn DefaultUni val, HasConstr val)
  => [Integer]
  -> Data
  -> BuiltinResult (OpaqueVConstr val)
matchData [] _ = fail "matchData requires a non-empty pattern table"
matchData encodedArities (Data.Constr tag fields) = do
  arities <-
    traverse
      ( \arity ->
          if 0 <= arity && arity <= toInteger (maxBound :: Int)
            then pure $ fromInteger arity
            else fail "matchData field count is outside the supported range"
      )
      encodedArities
  unless (0 <= tag && tag <= toInteger (maxBound :: Int)) $
    fail "No matchData constructor corresponds to the Data.Constr tag"
  expectedArity <- case drop (fromInteger tag) arities of
    arity : _ -> pure arity
    [] -> fail "No matchData constructor corresponds to the Data.Constr tag"
  unless (expectedArity == length fields) $
    fail "matchData payload length does not match the statically declared pattern arity"
  let resultTy :: forall tyname. Type tyname DefaultUni ()
      resultTy =
        TySOP () $ fmap (\arity -> replicate arity $ mkTyBuiltin @_ @Data ()) arities
  pure . OpaqueVConstr $ fromConstr resultTy (fromInteger tag) (fmap fromValue fields)
matchData _ _ = fail "matchData only supports Data.Constr"
