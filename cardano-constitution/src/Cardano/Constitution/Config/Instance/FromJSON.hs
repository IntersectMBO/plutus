{-# LANGUAGE LambdaCase #-}
-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Constitution.Config.Instance.FromJSON () where

import Cardano.Constitution.Config.Types

import PlutusPrelude (lowerInitialChar)
import PlutusTx.Ratio as Tx

import Control.Monad
import Data.Aeson.Key qualified as Aeson
import Data.Aeson.KeyMap qualified as Aeson
import Data.Aeson.Types as Aeson
import Data.Foldable
import Data.List as Haskell.List
import Data.Map qualified as M
import GHC.IsList
import Safe
import Text.Regex.TDFA as Rx

{-| Replica ADTs of ParamValue & ConstitutionConfig , specialised only for FromJSON.
Alternatively, we could generalise the aforementationed ADTs (needs barbies, breaks TxLifting) -}
data RawParamValue
  = RawParamInteger (Predicates Integer)
  | RawParamRational (Predicates Tx.Rational)
  | RawParamList (M.Map Integer RawParamValue)
  | RawParamAny

newtype RawConstitutionConfig = RawConstitutionConfig (M.Map Integer RawParamValue)

-- TODO: move to deriving-aeson
instance FromJSON PredKey where
  parseJSON = genericParseJSON (defaultOptions {constructorTagModifier = lowerInitialChar})

-- TODO: move to deriving-aeson
instance Aeson.FromJSONKey PredKey where
  fromJSONKey = genericFromJSONKey (defaultJSONKeyOptions {keyModifier = lowerInitialChar})

instance FromJSON a => FromJSON (Predicates a) where
  parseJSON val = do
    -- TODO: ugly code, refactor
    ms <- parseJSON @[Object] val
    -- filter out "$comment" from all keymaps
    let ms' = fmap (Object . Aeson.delete commentKey) ms
    -- re-parse correctly this time
    m <- parseJSON @[M.Map PredKey a] (Aeson.Array $ fromList ms')
    when (any ((/= 1) . length) m) $
      fail "Only one predicate-key per predicate inside the predicate list"
    pure $
      Predicates $
        -- using toAscList here ensures that the inner map is sorted
        M.toAscList
        -- combine the duplicate predicates into a list of predicate values
        -- entries with same key combine their values with (++)
        $
          M.unionsWith (<>) $
            fmap (fmap pure) m

instance FromJSON ConstitutionConfig where
  parseJSON =
    parseJSON -- first pass, parse raw
      >=> fromRaw -- second pass, flatten maps to lists, and check for contiguity

-- 1st pass
instance FromJSON RawConstitutionConfig where
  parseJSON =
    fmap RawConstitutionConfig
      . withObject "RawConstitutionConfig" (foldlM insertParam mempty . Aeson.toAscList)
    where
      insertParam acc (outerKey, outerValue) = do
        (index, msubIndex) <- parseParamKey outerKey
        when (index < 0) $ fail "Negative Integer ParamKey given"
        paramValue <- parseParamValue msubIndex outerValue
        -- flipped version of Lens.at
        M.alterF
          ( \case
              Nothing -> pure $ Just paramValue
              Just paramValue' -> Just <$> mergeParamValues paramValue' paramValue
          )
          index
          acc

-- second pass, flatten maps to lists, and check for contiguity
fromRaw :: MonadFail m => RawConstitutionConfig -> m ConstitutionConfig
fromRaw (RawConstitutionConfig rc) = ConstitutionConfig . M.toAscList <$> traverse flattenParamValue rc
  where
    flattenParamValue :: MonadFail m => RawParamValue -> m ParamValue
    flattenParamValue = \case
      RawParamList m -> do
        -- This is the CONTIGUOUS check.
        when (not $ M.keys m `isPrefixOf` [0 ..]) $ fail "The sub-indices are not in order."
        -- the M.elems will be in ascending order
        ParamList <$> traverse flattenParamValue (M.elems m)
      -- boilerplate follows
      RawParamInteger x -> pure $ ParamInteger x
      RawParamRational x -> pure $ ParamRational x
      RawParamAny -> pure ParamAny

-- MAYBE: use instead attoparsec-aeson.jsonWith/jsonNoDup to fail on parsing duplicate Keys,
-- because right now Aeson silently ignores duplicated param entries (arbitrarily picks the last of duplicates)
parseParamKey :: Aeson.Key -> Aeson.Parser (Integer, Maybe Integer)
parseParamKey (Aeson.toString -> s) = do
  -- MAYBE: fetch the regex pattern from the schema itself, it is easy
  [[_, indexS, _, subIndexS]] :: [[String]] <- s Rx.=~~ ("^(0|[1-9][0-9]*)(\\[(0|[1-9][0-9]*)\\])?$" :: String)
  indexI <- either fail pure $ readEitherSafe indexS
  mSubIndexI <-
    if null subIndexS
      then pure Nothing
      else Just <$> either fail pure (readEitherSafe subIndexS)
  pure (indexI, mSubIndexI)

{-| If there is a subkey given, treat the param as a paramlist
Otherwise, parse it based on the json's "type" -}
parseParamValue :: Maybe ParamKey -> Value -> Parser RawParamValue
parseParamValue = \case
  Nothing -> parseTypedParamValue
  -- if we parsed a sub-index, treat the param value as a `M.singleton subIndex value`
  Just subIndex -> fmap (RawParamList . M.singleton subIndex) . parseTypedParamValue
  where
    parseTypedParamValue :: Value -> Parser RawParamValue
    parseTypedParamValue = withObject "RawParamValue" $ \o -> do
      ty <- o .: typeKey
      parseSynonymType ty o

    -- the base types we support
    parseBaseType :: Key -> Object -> Parser RawParamValue
    parseBaseType ty o = case ty of
      "integer" -> RawParamInteger <$> (o .: predicatesKey)
      -- NOTE: even if the Tx.Ratio.Rational constructor is not exposed, the 2 arguments to the constructor
      -- will be normalized (co-primed) when Tx.lift is called on them.
      -- SO there is no speed benefit to statically co-prime them ourselves for efficiency.
      "rational" -> RawParamRational <$> (o .: predicatesKey)
      "any" -> pure RawParamAny
      _ -> fail "invalid type tag"

    -- synonyms to ease the transition from cddl
    parseSynonymType = \case
      "coin" -> parseBaseType "integer"
      "uint.size4" -> parseBaseType "integer"
      "uint.size2" -> parseBaseType "integer"
      "uint" -> parseBaseType "integer" -- For ex units
      "epoch_interval" -> parseBaseType "integer" -- Rename of uint.size4
      "unit_interval" -> parseBaseType "rational"
      "nonnegative_interval" -> parseBaseType "rational"
      "costMdls" -> parseBaseType "any"
      x -> parseBaseType x -- didn't find synonym, try as basetype

-- | It is like an `mappend` when both inputs are ParamList's.
mergeParamValues :: MonadFail m => RawParamValue -> RawParamValue -> m RawParamValue
mergeParamValues (RawParamList m1) = \case
  RawParamList m2 -> pure $ RawParamList $ m1 <> m2
  _ -> fail "param matched with subparam"
mergeParamValues _ = \case
  RawParamList _ -> fail "param matched with subparam"
  -- in reality this cannot be triggered, because we would then have duplicate params
  -- , which default aeson and json allow
  _ -> fail "this should not happen"

predicatesKey, typeKey, commentKey :: Aeson.Key
predicatesKey = "predicates"
typeKey = "type"
commentKey = "$comment"
