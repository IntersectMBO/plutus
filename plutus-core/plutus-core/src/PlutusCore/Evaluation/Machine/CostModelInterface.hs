-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}

module PlutusCore.Evaluation.Machine.CostModelInterface
    ( CostModelParams
    , CekMachineCosts
    , extractCostModelParams
    , applyCostModelParams
    , CostModelApplyError (..)
    , CostModelApplyWarn (..)
    )
where

import PlutusCore.Evaluation.Machine.MachineParameters (CostModel (..))
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts,
                                                                 cekMachineCostsPrefix)

import Control.Exception
import Control.Monad.Except
import Data.Aeson
import Data.Aeson.Flatten
import Data.Data (Data)
import Data.HashMap.Strict qualified as HM
import Data.Map qualified as Map
import Data.Map.Merge.Lazy qualified as Map
import Data.Text qualified as Text
import Prettyprinter

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
programs whose cost reaches MaxBound will fail due to excessive resource usage.

3. BuiltinCostModel includes the *type* of the model, which isn't a parameter

We can just strip the type out, but in particular this means that the parameters are
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

{- Note [Cost model parameters from the ledger's point of view]

A newly-voted protocol update may have some of the following effects:

a) Introduce a new plutus-language version accompanied by a whole new set of cost model parameters for that new version.
b) Update any values of existing cost model parameters for an existing plutus version.
c) Bring new builtins to an existing plutus version, thus also extending
the set of current cost model parameters of that version with new parameters for the new builtins.

Note that, removing existing builtins is only possible by issuing a brand-new plutus language version
that would exclude them (and their cost model parameters).
An alternative without issuing a new protocol update and affecting a current version,
would be to set via (b) the builtins' cost model parameters prohibitively high,
so as to make those builtins impossible to execute given the current maximum transaction budget,
thus effectively disabling their execution.

The ledger-state stores a *mapping* of each plutus-language version to its current set of cost model parameters.
Each set of parameters is represented as an *array of plain integer values*,
without the  cost model parameter names. Overall this ledger-state can be conceptualized as `Map PlutusVersion [Integer]`.

The implementation of (a) and (b) effects by the node software is straightforward:
for (a) introduce a whole new entry to the Map; for (b) update the affected array in-place with the new values.
As a consequence for implementing (c), we arrive to four restrictions that hold for ALL protocol updates:

1) In case of (b), the values of the existing parameters may change, but their *meaning*,
i.e. which parameter name and thus which builtin parameter they correspond to,  ABSOLUTELY CANNOT change. In other words,
the existing parameters cannot be re-ordered.

2) In case of (c) the new parameters (for the new builtins) must be appended **to the end** of the existing array for the affected version.

3) The node software is responsible to re-create the plutus runtimes when a new protocol is voted in ---
one plutus runtime a.k.a. `plutus-ledger-api.EvaluationContext` per plutus-version.

4) The node software will always pass the array in its entirety to each plutus-runtime,
and not partially just the updated-parameter values (in case of (b)) or just the new-parameter values (in case of (c)).

There is one complication when (c) happens and some running nodes are not updated:
these nodes are only aware of the old set of builtins, thus they expect a specific (fixed in software)
number of cost model parameters.
To guarantee smooth,continuous operation of the entire network (and not cause any splits)
we allow the old nodes to continue operating when receiving more cost model parameters
than they expected, and only issue a warning to them. When the nodes restart and update to the new node software
these warnings will go away. The overall logic for the expected number of cost model paremeters is as follows:

(expected number in node software == received number by ledger) => NOWARNING & NOERROR
(expected number in node software < received number by ledger)  => WARNING
(expected number in node software > received number by ledger)  => ERROR

If the received number is EQ or GT the expected (WARNING), the plutus software
will take the first n from the received cost model parameters (n==expected number),
and create the internal (nameful) representation of cost model parameters, by assigning a parameter name
to its value: see `PlutusLedgerApi.Common.ParamName.tagWithParamNames` and the `ParamName` datatypes in
plutus-ledger-api.

-}


{-| A raw representation of the ledger's cost model parameters.

The associated keys/names to the parameter values are arbitrarily set by the plutus team; the ledger does not hold any such names.

See Note [Cost model parameters]
-}
type CostModelParams = Map.Map Text.Text Integer

-- See Note [Cost model parameters]
-- | Extract the model parameters from a model.
extractParams :: ToJSON a => a -> Maybe CostModelParams
extractParams cm = case toJSON cm of
    Object o ->
        let
            flattened = objToHm $ flattenObject "-" o
            usingCostingIntegers = HM.mapMaybe (\case { Number n -> Just $ ceiling n; _ -> Nothing }) flattened
            -- ^ Only (the contents of) the "Just" values are retained in the output map.
            mapified = Map.fromList $ HM.toList usingCostingIntegers
        in Just mapified
    _ -> Nothing


-- | A fatal error when trying to create a cost given some plain costmodel parameters.
data CostModelApplyError =
      CMUnknownParamError !Text.Text
      -- ^ a costmodel parameter with the give name does not exist in the costmodel to be applied upon
    | CMInternalReadError
      -- ^ internal error when we are transforming the applyParams' input to json (should not happen)
    | CMInternalWriteError !String
      -- ^ internal error when we are transforming the applied params from json with given jsonstring error (should not happen)
    | CMTooFewParamsError { cmTooFewExpected :: !Int, cmTooFewActual :: !Int }
      -- ^ See Note [Cost model parameters from the ledger's point of view]
    deriving stock (Eq, Show, Data)
    deriving anyclass Exception

-- | A non-fatal warning when trying to create a cost given some plain costmodel parameters.
data CostModelApplyWarn =
    CMTooManyParamsWarn { cmTooManyExpected :: !Int, cmTooManyActual :: !Int }
    {- ^ More costmodel parameters given, than expected

    See Note [Cost model parameters from the ledger's point of view]
    -}

instance Pretty CostModelApplyError where
    pretty = (preamble <+>) . \case
        CMUnknownParamError k -> "Unknown cost model parameter:" <+> pretty k
        CMInternalReadError      -> "Internal problem occurred upon reading the given cost model parameteres"
        CMInternalWriteError str     -> "Internal problem occurred upon generating the applied cost model parameters with JSON error:" <+> pretty str
        CMTooFewParamsError{..}     -> "Too few cost model parameters passed, expected" <+> pretty cmTooFewExpected <+> "but got" <+> pretty cmTooFewActual
      where
          preamble = "applyParams error:"

instance Pretty CostModelApplyWarn where
    pretty = (preamble <+>) . \case
        CMTooManyParamsWarn{..} -> "Too many cost model parameters passed, expected" <+> pretty cmTooManyExpected <+> "but got" <+> pretty cmTooManyActual
      where
          preamble = "applyParams warn:"

-- See Note [Cost model parameters]
-- | Update a model by overwriting the parameters with the given ones.
applyParams :: (FromJSON a, ToJSON a, MonadError CostModelApplyError m)
            => a
            -> CostModelParams
            -> m a
applyParams cm params = case toJSON cm of
    Object o ->
        let
            usingScientific = fmap (Number . fromIntegral) params
            flattened = fromHash $ objToHm $ flattenObject "-" o
        in do
            -- this is where the overwriting happens
            -- fail when key is in params (left) but not in the model (right)
            merged <- Map.mergeA failMissing Map.preserveMissing (Map.zipWithMatched leftBiased) usingScientific flattened
            let unflattened = unflattenObject "-" $ hmToObj $ toHash merged
            case fromJSON (Object unflattened) of
                Success a -> pure a
                Error str -> throwError $ CMInternalWriteError str
    _ -> throwError CMInternalReadError
  where
    toHash = HM.fromList . Map.toList
    fromHash = Map.fromList . HM.toList
    -- fail when field missing
    failMissing = Map.traverseMissing $ \ k _v -> throwError $ CMUnknownParamError k
    -- left-biased merging when key found in both maps
    leftBiased _k l _r = l


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
    Map.union <$> extractParams (_machineCostModel model) <*> extractParams (_builtinCostModel model)

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
    :: (FromJSON evaluatorcosts, FromJSON builtincosts, ToJSON evaluatorcosts, ToJSON builtincosts, MonadError CostModelApplyError m)
    => Text.Text
    -> CostModel evaluatorcosts builtincosts
    -> CostModelParams
    -> m (CostModel evaluatorcosts builtincosts)
applySplitCostModelParams prefix model params =
    let SplitCostModelParams machineparams builtinparams = splitParams prefix params
    in CostModel <$> applyParams (_machineCostModel model) machineparams
                 <*> applyParams (_builtinCostModel model) builtinparams

-- | Update a CostModel for the CEK machine with a given set of parameters.
-- Note that this is costly. See [here](https://github.com/input-output-hk/plutus/issues/4962).
-- Callers are recommended to call this once and cache the results.
applyCostModelParams
    :: (FromJSON evaluatorcosts, FromJSON builtincosts, ToJSON evaluatorcosts, ToJSON builtincosts, MonadError CostModelApplyError m)
    => CostModel evaluatorcosts builtincosts
    -> CostModelParams
    -> m (CostModel evaluatorcosts builtincosts)
applyCostModelParams = applySplitCostModelParams cekMachineCostsPrefix
