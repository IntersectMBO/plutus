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
import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts ()

import           Data.Aeson
import           Data.Aeson.Flatten
import qualified Data.HashMap.Strict                                      as HM
import qualified Data.Map                                                 as Map
import qualified Data.Scientific                                          as S
import qualified Data.Text                                                as Text


{- Note [Cost model parameters]
We want to expose to the ledger some notion of the "cost model
parameters". Intuitively, these should be all the numbers that appear in the
cost model.

However, there are quite a few quirks to deal with.

1. BuiltinCostModel is stuctured

That is, it's a complex data structure and the numbers in question are often
nested inside it.  To deal with this quickly, we take the ugly approach of
operating on the JSON representation of the model.  We flatten this down into a
simple key-value mapping (see 'flattenObject' and 'unflattenObject'), and then
look only at the numbers.

2. We use floats, not integers

We'd really prefer to expose integers as our parameters - they're just better
behaved, and really we'd like to use integers internally too for determinism
reasons. So we pretend that we have integers by scaling up all our numbers by
1000*1000 and taking the integral floor, at some loss of precision.

Once we use integers internally this will be simpler.

3. BuiltinCostModel includes the *type* of the model, which isn't a parameter

We can just strip the out, but in particular this means that the parameters are
not enough to *construct* a model.  So we punt and say that you can *update* a
model by giving the parameters. So you can take the default model and then
overwrite the parameters, which seems okay.

This is also implemented in a horrible JSON-y way.

4. The implementation is not nice

Ugly JSON stuff and failure possibilities where there probably shouldn't be any.

5. The overall cost model now includes two components: a model for the internal
costs of the evaluator and a model for built-in evaluation costs.  We just
re-use the technique mentioned above to extract parameters for the evaluator
costs, packing these together with the parameters for the builtin cost model to
obtain parameters for the overall model
-}

-- See Note [Cost model parameters]
type ModelParams = Map.Map Text.Text Integer

-- See Note [Cost model parameters]
-- | Extract the model parameters from a model.
extractParams :: ToJSON a => a -> Maybe ModelParams
extractParams cm = case toJSON cm of
    Object o ->
        let
            flattened = flattenObject "-" o
            toScaledInteger :: S.Scientific -> Integer
            toScaledInteger n = floor (n*1000*1000)
            scaledNumbers = HM.mapMaybe (\case { Number n -> Just $ toScaledInteger n; _ -> Nothing }) flattened
            mapified = Map.fromList $ HM.toList scaledNumbers
        in Just mapified
    _ -> Nothing


-- See Note [Cost model parameters]
-- | Update a model by overwriting the parameters with the given ones.
applyParams :: (FromJSON a, ToJSON a) => a -> ModelParams -> Maybe a
applyParams cm params = case toJSON cm of
    Object o ->
        let
            hashmapified = HM.fromList $ Map.toList params
            scaledNumbers = fmap (\n -> Number $ fromIntegral n / (1000*1000)) hashmapified
            flattened = flattenObject "-" o
            -- this is where the overwriting happens, this is left-biased
            merged = HM.union scaledNumbers flattened
            unflattened = unflattenObject "-" merged
        in case fromJSON (Object unflattened) of
            Success a -> Just a
            Error _   -> Nothing
    _ -> Nothing


-- | Parameters for a model with components for both machine costs and builtin costs
data CostModelParams = CostModelParams {
      machineCostModelParams :: ModelParams  -- Not to be confused with MachineParameters, which is used during script evaluation.
    , builtinCostModelParams :: ModelParams
    }

extractCostModelParams :: ToJSON machinecosts => CostModel machinecosts -> Maybe (CostModelParams)
extractCostModelParams cm =
    case ( extractParams (machineCostModel cm)
         , extractParams (builtinCostModel cm) )
    of (Just machineParams, Just builtinParams) -> Just $ CostModelParams machineParams builtinParams
       _                                        -> Nothing

applyCostModelParams
    :: (FromJSON evaluatorcosts, ToJSON evaluatorcosts)
    => CostModel evaluatorcosts
    -> CostModelParams
    -> Maybe (CostModel evaluatorcosts)
applyCostModelParams cm cmdata =
    case ( applyParams (machineCostModel cm) (machineCostModelParams cmdata)
         , applyParams (builtinCostModel cm) (builtinCostModelParams cmdata) )
    of
      (Just machineCosts, Just buitinCosts) -> Just $ CostModel machineCosts buitinCosts
      _                                     -> Nothing
