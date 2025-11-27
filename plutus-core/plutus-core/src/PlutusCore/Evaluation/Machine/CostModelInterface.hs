-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

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
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
  ( CekMachineCosts
  , cekMachineCostsPrefix
  )

import Control.DeepSeq (NFData)
import Control.Exception
import Control.Monad.Except
import Data.Aeson
import Data.Aeson.Flatten
import Data.Data (Data)
import Data.HashMap.Strict qualified as HM
import Data.Int (Int64)
import Data.Map qualified as Map
import Data.Map.Merge.Lazy qualified as Map
import Data.Text qualified as Text
import GHC.Generics (Generic)
import NoThunks.Class
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

To make (c) work, we must allow a node to continue operating when receiving either more or
fewer cost model parameters than it expects. As an example, suppose at the beginning of
major protocol version 9 (PV9), PlutusV3 has 100 cost model parameters. During PV9, we add
some more builtins to Plutus V3 (to be enabled after the hard fork, at PV10), requiring 20
additional cost model parameters. Then, one submits a proposal updating the number of PlutusV3
cost model parameters to 120.

During PV9, both node-9.x and node-10.x must operate normally and agree on everything. This means
node-9.x must allow receiving more cost model parameters than it expects (since it may receive
120), and node-10.x must allow receiving fewer than it expects (since it may receive 100).
Node-10.x should fill in the missing parameters with a large enough number to prevent the new
builtins from being used, in case the hard fork to PV10 happens without first updating the number
of PlutusV3 cost model parameters to 120 (which is unlikely to happen, but just in case).

During PV10, node-9.x stops working.

The overall logic for the expected number of cost model paremeters is as follows:

(expected number in node software == received number by ledger) => NOWARNING & NOERROR
(expected number in node software < received number by ledger)  => WARNING
(expected number in node software > received number by ledger)  => WARNING

If the received number is EQ or GT the expected (WARNING), we
will take the first n from the received cost model parameters (n==expected number),
and create the internal (nameful) representation of cost model parameters, by assigning a parameter name
to its value: see `PlutusLedgerApi.Common.ParamName.tagWithParamNames` and the `ParamName` datatypes in
plutus-ledger-api.

If the received number is LT the expected (WARNING), we will fill in the missing parameters
with maxBound :: Int64.

See https://github.com/IntersectMBO/cardano-ledger/issues/2902 for a discussion
of these issues and the rationale for adopting the system described above.

-}

{- Note [Table of all possible ledger's states w.r.t. cost model parameters update]
What Note [Cost model parameters from the ledger's point of view] says can be summarized in a table.
We'll need to enumerate all possible combinations of

    old_node / new_node
    before_HF / after_HF
    shorter_list / exact_list / longer_list

where the last ones are about the list of cost model parameters supplied by the ledger, e.g.
@shorter_list@ means that the ledger supplied a list of cost model parameters that is shorter than
expected by the appropriate Plutus ledger language at the specific protocol version.

Note that the exact same list may be @exact_list@ for @old_node@ and @shorter_list@ for @new_node@.
And the exact same list may be @longer_list@ for @old_node@ and @exact_list@ for @new_node@.

We'll also need to consider changing the cost model parameters of old builtins and adding cost model
parameters for new builtins separately, because there are non-trivial differences. For old builtins
we'll only consider the case of adding new cost model parameters, because the case of reducing the
number of cost model parameters is trivial: the only thing we can do about it is simply keeping the
redundant arguments and asking the ledger to continue providing them, as there's no way for us to
remove them form the middle of the cost model parameter list. And if the number of parameters
doesn't change, then there's nothing to worry about.

We'll also only consider the case when the Plutus ledger language stays the same, because if it
changes, then everything becomes trivial: we don't need to worry about any backward compatibility
and can simply "start over" for a new ledger language.

"OK" in the table below means "we handle this situation correctly as implied by
Note [Cost model parameters from the ledger's point of view]".

The table then looks like this:

                                         old_builtin new_builtin
    old_node / before_HF / shorter_list    OK [1]      OK [1]
    old_node / before_HF / exact_list      OK [2]      OK [3]
    old_node / before_HF / longer_list     OK [4]      OK [3]

    old_node / after_HF / shorter_list     OK [5]      OK [5]
    old_node / after_HF / exact_list       OK [5]      OK [5]
    old_node / after_HF / longer_list      OK [5]      OK [5]

    new_node / before_HF / shorter_list    OK [6]      OK [3]
    new_node / before_HF / exact_list      OK [2]      OK [3]
    new_node / before_HF / longer_list     OK [7]      OK [7]

    new_node / after_HF / shorter_list     OK [8]      OK [9]
    new_node / after_HF / exact_list       OK [2]      OK [2]
    new_node / after_HF / longer_list      OK [10]     OK [10]

[1] this is the same case as `new_node / after_HF / shorter_list`, just in the context of a different hardfork
[2] the most straightforward case, nothing to consider
[3] a new builtin cannot be used before the hardfork as `scriptCBORDecoder` will fail with "built-in function X is not available"
[4] an old builtin does not touch its new cost model parameters (if any) before the hardfork, hence it's safe to ignore those extra parameters
[5] the old node is not alive after the hardfork, hence anything is OK
[6] an old builtin does not touch its new cost model parameters (if any) before the hardfork, hence it's safe to make those extra parameters all `maxBound`
[7] this is a bit weird, but theoretically possible (one can propose protocol parameter updates, including updating the number of PlutusV3 cost model parameters to 100000, or updating the max block size to 0. Those will be rejected, especially if there's a guardrail in place). But even it happens in practice, `longer_list` should never be a problem, since the extra numbers are simply ignored
[8] this is a tricky one: since it's a shorter list, the missing cost model parameters all become 'maxBound' meaning for an old builtin we end up in a situation where some of its cost model parameters are 'maxBound' and some are not, which is not enough to prevent the builtin from running. Which is however not a problem, because it _is_ fine to run the builtin after the hardfork, all we care about is that it's not undercosted and making some of the cost model parameters 'maxBound' ensures that it's not as it's literally the highest value that they can have
[9] same as [8] except this does ensure that the builtin never runs, because all of its cost model parameters are 'maxBound', which makes the cost of the builtin higher than any reasonable budget
[10] this is the same case as `old_node / before_HF / longer_list`, just in the context of a different hardfork
-}

{-| A raw representation of the ledger's cost model parameters.

The associated keys/names to the parameter values are arbitrarily set by the plutus team; the ledger does not hold any such names.

See Note [Cost model parameters] -}
type CostModelParams = Map.Map Text.Text Int64

-- See Note [Cost model parameters]
-- | Extract the model parameters from a model.
extractParams :: ToJSON a => a -> Maybe CostModelParams
extractParams cm = case toJSON cm of
  Object o ->
    let
      flattened = objToHm $ flattenObject "-" o
      usingCostingIntegers = HM.mapMaybe (\case Number n -> Just $ ceiling n; _ -> Nothing) flattened
      -- \^ Only (the contents of) the "Just" values are retained in the output map.
      mapified = Map.fromList $ HM.toList usingCostingIntegers
     in
      Just mapified
  _ -> Nothing

-- | A fatal error when trying to create a cost given some plain costmodel parameters.
data CostModelApplyError
  = -- | a costmodel parameter with the give name does not exist in the costmodel to be applied upon
    CMUnknownParamError !Text.Text
  | -- | internal error when we are transforming the applyParams' input to json (should not happen)
    CMInternalReadError
  | -- | internal error when we are transforming the applied params from json with given jsonstring error (should not happen)
    CMInternalWriteError !String
  deriving stock (Eq, Show, Generic, Data)
  deriving anyclass (Exception, NFData, NoThunks)

-- | A non-fatal warning when trying to create a cost given some plain costmodel parameters.
data CostModelApplyWarn
  = -- | See Note [Cost model parameters from the ledger's point of view]
    CMTooManyParamsWarn {cmExpected :: !Int, cmActual :: !Int}
  | -- | See Note [Cost model parameters from the ledger's point of view]
    CMTooFewParamsWarn {cmExpected :: !Int, cmActual :: !Int}

instance Pretty CostModelApplyError where
  pretty =
    (preamble <+>) . \case
      CMUnknownParamError k -> "No such parameter in target cost model:" <+> pretty k
      CMInternalReadError -> "Internal problem occurred upon reading the given cost model parameters"
      CMInternalWriteError str -> "Internal problem occurred upon generating the applied cost model parameters with JSON error:" <+> pretty str
    where
      preamble = "applyParams error:"

instance Pretty CostModelApplyWarn where
  pretty =
    (preamble <+>) . \case
      CMTooManyParamsWarn {..} -> "Too many cost model parameters passed, expected" <+> pretty cmExpected <+> "but got" <+> pretty cmActual
      CMTooFewParamsWarn {..} -> "Too few cost model parameters passed, expected" <+> pretty cmExpected <+> "but got" <+> pretty cmActual
    where
      preamble = "applyParams warn:"

-- See Note [Cost model parameters]
-- | Update a model by overwriting the parameters with the given ones.
applyParams
  :: (FromJSON a, ToJSON a, MonadError CostModelApplyError m)
  => a
  -> CostModelParams
  -> m a
applyParams cm params = case toJSON cm of
  Object o ->
    let
      usingScientific = fmap (Number . fromIntegral) params
      flattened = fromHash $ objToHm $ flattenObject "-" o
     in
      do
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
    failMissing = Map.traverseMissing $ \k _v -> throwError $ CMUnknownParamError k
    -- left-biased merging when key found in both maps
    leftBiased _k l _r = l

-- | Parameters for a machine step model and a builtin evaluation model bundled together.
data SplitCostModelParams
  = SplitCostModelParams
  { _machineParams :: CostModelParams
  , _builtinParams :: CostModelParams
  }

{-| Split a CostModelParams object into two subobjects according to some prefix:
see item 5 of Note [Cost model parameters]. -}
splitParams :: Text.Text -> CostModelParams -> SplitCostModelParams
splitParams prefix params =
  let (machineparams, builtinparams) = Map.partitionWithKey (\k _ -> Text.isPrefixOf prefix k) params
   in SplitCostModelParams machineparams builtinparams

-- | Given a CostModel, produce a single map containing the parameters from both components
extractCostModelParams
  :: (ToJSON machinecosts, ToJSON builtincosts)
  => CostModel machinecosts builtincosts -> Maybe CostModelParams
extractCostModelParams model =
  -- this is using the applicative instance of Maybe
  Map.union <$> extractParams (_machineCostModel model) <*> extractParams (_builtinCostModel model)

{-| Given a set of cost model parameters, split it into two parts according to
some prefix and use those parts to update the components of a cost model. -}

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
   in CostModel
        <$> applyParams (_machineCostModel model) machineparams
        <*> applyParams (_builtinCostModel model) builtinparams

{-| Update a CostModel for the CEK machine with a given set of parameters.
Note that this is costly. See [here](https://github.com/IntersectMBO/plutus/issues/4962).
Callers are recommended to call this once and cache the results. -}
applyCostModelParams
  :: (FromJSON evaluatorcosts, FromJSON builtincosts, ToJSON evaluatorcosts, ToJSON builtincosts, MonadError CostModelApplyError m)
  => CostModel evaluatorcosts builtincosts
  -> CostModelParams
  -> m (CostModel evaluatorcosts builtincosts)
applyCostModelParams = applySplitCostModelParams cekMachineCostsPrefix
