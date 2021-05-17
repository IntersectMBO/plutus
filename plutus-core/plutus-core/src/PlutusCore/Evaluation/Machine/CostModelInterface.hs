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
reasons. So we pretend that we have integers by scaling up all our numbers by a
large power of 10 (see scaleFactor below) and taking the integral floor, at some
loss of precision.

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
costs, merging these with the parameters for the builtin cost model to obtain
parameters for the overall model.  To recover cost model components we assume
that every field in the cost model for the evaluator begins with a prefix (eg
"cek") which is does not occur as a prefix of any built-in function, and use
that to split the map of parameters into two maps.

-}

-- | See point 3 of Note [Cost model parameters]
-- Some of the numbers in the cost model are of the order or 1e-7 or 1e-8, and
-- we need a large scale factor to avoid truncating a significant number of
-- digits.
scaleFactor :: S.Scientific
scaleFactor = 1e20

-- See Note [Cost model parameters]
type CostModelParams = Map.Map Text.Text Integer

-- See Note [Cost model parameters]
-- | Extract the model parameters from a model.
extractParams :: ToJSON a => a -> Maybe CostModelParams
extractParams cm = case toJSON cm of
    Object o ->
        let
            flattened = flattenObject "-" o
            toScaledInteger :: S.Scientific -> Integer
            toScaledInteger n = floor (n*scaleFactor)
            scaledNumbers = HM.mapMaybe (\case { Number n -> Just $ toScaledInteger n; _ -> Nothing }) flattened
            mapified = Map.fromList $ HM.toList scaledNumbers
        in Just mapified
    _ -> Nothing


-- See Note [Cost model parameters]
-- | Update a model by overwriting the parameters with the given ones.
applyParams :: (FromJSON a, ToJSON a) => a -> CostModelParams -> Maybe a
applyParams cm params = case toJSON cm of
    Object o ->
        let
            hashmapified = HM.fromList $ Map.toList params
            scaledNumbers = fmap (\n -> Number $ fromIntegral n / scaleFactor) hashmapified
            flattened = flattenObject "-" o
            -- this is where the overwriting happens, this is left-biased
            merged = HM.union scaledNumbers flattened
            unflattened = unflattenObject "-" merged
        in case fromJSON (Object unflattened) of
            Success a -> Just a
            Error _   -> Nothing
    _ -> Nothing

-- | Parameters for a machine step model and a builtin evaluation model bundled together.
data SplitCostModelParams =
    SplitCostModelParams {
      machineParams :: CostModelParams
    , builtinParams :: CostModelParams
    }

-- | Split a CostModelParams object into two subobjects according to some prefix:
-- see item 5 of Note [Cost model parameters].
splitParams :: Text.Text -> CostModelParams -> SplitCostModelParams
splitParams prefix params =
    let machineparams = Map.filterWithKey (\k _ ->       Text.isPrefixOf prefix k) params
        builtinparams = Map.filterWithKey (\k _ -> not $ Text.isPrefixOf prefix k) params
    in SplitCostModelParams machineparams builtinparams

-- | Given a CostModel, produce a single map containing the parameters from both components
extractCostModelParams :: ToJSON machinecosts => CostModel machinecosts -> Maybe CostModelParams
extractCostModelParams model =
    case ( extractParams (machineCostModel model)
         , extractParams (builtinCostModel model) )
    of (Just machineparams, Just builtinparams) -> Just $ Map.union machineparams builtinparams
       _                                        -> Nothing

-- | Given a set of cost model parameters, split it into two parts according to some
-- prefix and use those parts to update the components of a cost model.
applySplitCostModelParams
    :: (FromJSON evaluatorcosts, ToJSON evaluatorcosts)
    => Text.Text
    -> CostModel evaluatorcosts
    -> CostModelParams
    -> Maybe (CostModel evaluatorcosts)
applySplitCostModelParams prefix model params =
    let p = splitParams prefix params
    in case ( applyParams (machineCostModel model) (machineParams p)
            , applyParams (builtinCostModel model) (builtinParams p) )
       of
         (Just machineCosts, Just buitinCosts) -> Just $ CostModel machineCosts buitinCosts
         _                                     -> Nothing

-- | Update a CostModel for the CEK machine with a given set of parameters,
applyCostModelParams
    :: (FromJSON evaluatorcosts, ToJSON evaluatorcosts)
    => CostModel evaluatorcosts
    -> CostModelParams
    -> Maybe (CostModel evaluatorcosts)
applyCostModelParams = applySplitCostModelParams cekMachineCostsPrefix
