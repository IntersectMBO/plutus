{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Evaluation.Machine.CostModelInterface
    ( CostModelParams
    , extractCostModelParams
    , applyCostModelParams
    )
where

import           PlutusCore.Evaluation.Machine.BuiltinCostModel           ()
import           PlutusCore.Evaluation.Machine.MachineParameters          (CostModel (..))
import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (cekMachineCostsPrefix)

import           Data.Aeson
import           Data.Aeson.Flatten
import qualified Data.HashMap.Strict                                      as HM
import qualified Data.Map                                                 as Map
import qualified Data.Text                                                as Text


{- Note [Cost model parameters]
We want to expose to the ledger some notion of the "cost model
parameters". Intuitively, these should be all the numbers that appear in the
cost model.

However, there are quite a few quirks to deal with.

1. BuiltinCostModel is stuctured.

That is, it's a complex data structure and the numbers in question are often
nested inside it.  To deal with this quickly, we take the ugly approach of
operating on the JSON representation of the model.  We flatten this down into a
simple key-value mapping (see 'flattenObject' and 'unflattenObject'), and then
look only at the numbers.

2. We use CostingIntegers, Aeson uses Data.Scientific.

The numbers in CostModel objects are CostingIntegers, which are usually the
64-bit SatInt type (but Integer on 32-bit machines).  Numerical values in
Aeson-encoded JSON objects are represented as Data.Scientific (Integer mantissa,
Int exponent). We should be able to convert between these types without loss of
precision, except that Scientific numbers of large magnitude will overflow to
SatInt::MaxBound or underflow to SatInt::MinBound.  This is OK because
CostModelParams objects should never contain such large numbers. Any Plutus Core
programs whose cost reaches MaxBound will fail due to excesssive resource usage.

3. BuiltinCostModel includes the *type* of the model, which isn't a parameter

We can just strip the out, but in particular this means that the parameters are
not enough to *construct* a model.  So we punt and say that you can *update* a
model by giving the parameters. So you can take the default model and then
overwrite the parameters, which seems okay.

This is also implemented in a horrible JSON-y way.

4. The implementation is not nice.

Ugly JSON stuff and failure possibilities where there probably shouldn't be any.

5. The overall cost model now includes two components: a model for the internal
costs of the evaluator and a model for built-in evaluation costs.  We just
re-use the technique mentioned above to extract parameters for the evaluator
costs, merging these with the parameters for the builtin cost model to obtain
parameters for the overall model.  To recover cost model components we assume
that every field in the cost model for the evaluator begins with a prefix (eg
"cek") which is does not occur as a prefix of any built-in function, and use
that to split the map of parameters into two maps.

-}

-- See Note [Cost model parameters]
type CostModelParams = Map.Map Text.Text Integer

-- See Note [Cost model parameters]
-- | Extract the model parameters from a model.
extractParams :: ToJSON a => a -> Maybe CostModelParams
extractParams cm = case toJSON cm of
    Object o ->
        let
            flattened = flattenObject "-" o
            usingCostingIntegers = HM.mapMaybe (\case { Number n -> Just $ ceiling n; _ -> Nothing }) flattened
            -- ^ Only (the contents of) the "Just" values are retained in the output map.
            mapified = Map.fromList $ HM.toList usingCostingIntegers
        in Just mapified
    _ -> Nothing


-- See Note [Cost model parameters]
-- | Update a model by overwriting the parameters with the given ones.
applyParams :: (FromJSON a, ToJSON a) => a -> CostModelParams -> Maybe a
applyParams cm params = case toJSON cm of
    Object o ->
        let
            hashmapified = HM.fromList $ Map.toList params
            usingScientific = fmap (Number . fromIntegral) hashmapified
            flattened = flattenObject "-" o
            -- this is where the overwriting happens, this is left-biased
            merged = HM.union usingScientific flattened
            unflattened = unflattenObject "-" merged
        in case fromJSON (Object unflattened) of
            Success a -> Just a
            Error _   -> Nothing
    _ -> Nothing

-- | Parameters for a machine step model and a builtin evaluation model bundled together.
data SplitCostModelParams =
    SplitCostModelParams {
      _machineParams :: CostModelParams
    , _builtinParams :: CostModelParams
    }

-- | Split a CostModelParams object into two subobjects according to some prefix:
-- see item 5 of Note [Cost model parameters].
splitParams :: Text.Text -> CostModelParams -> SplitCostModelParams
splitParams prefix params =
    let (machineparams, builtinparams) = Map.partitionWithKey (\k _ -> Text.isPrefixOf prefix k) params
    in SplitCostModelParams machineparams builtinparams

-- | Given a CostModel, produce a single map containing the parameters from both components
extractCostModelParams
    :: (ToJSON machinecosts, ToJSON builtincosts)
    => CostModel machinecosts builtincosts -> Maybe CostModelParams
extractCostModelParams model = -- this is using the applicative instance of Maybe
    Map.union <$> extractParams (machineCostModel model) <*> extractParams (builtinCostModel model)

-- | Given a set of cost model parameters, split it into two parts according to
-- some prefix and use those parts to update the components of a cost model.
{- Strictly we don't need to do the splitting: when we call fromJSON in
   applyParams any superfluous objects in the map being decoded will be
   discarded, so we could update both components of the cost model with the
   entire set of parameters without having to worry about splitting the
   parameters on a prefix of the key.  This relies on what appears to be an
   undocumented implementation choice in Aeson though (other JSON decoders (for
   other languages) seem to vary in how unknown fields are handled), so let's be
   explicit. -}
applySplitCostModelParams
    :: (FromJSON evaluatorcosts, FromJSON builtincosts, ToJSON evaluatorcosts, ToJSON builtincosts)
    => Text.Text
    -> CostModel evaluatorcosts builtincosts
    -> CostModelParams
    -> Maybe (CostModel evaluatorcosts builtincosts)
applySplitCostModelParams prefix model params =
    let SplitCostModelParams machineparams builtinparams = splitParams prefix params
    in CostModel <$> applyParams (machineCostModel model) machineparams
                 <*> applyParams (builtinCostModel model) builtinparams

-- | Update a CostModel for the CEK machine with a given set of parameters,
applyCostModelParams
    :: (FromJSON evaluatorcosts, FromJSON builtincosts, ToJSON evaluatorcosts, ToJSON builtincosts)
    => CostModel evaluatorcosts builtincosts
    -> CostModelParams
    -> Maybe (CostModel evaluatorcosts builtincosts)
applyCostModelParams = applySplitCostModelParams cekMachineCostsPrefix
