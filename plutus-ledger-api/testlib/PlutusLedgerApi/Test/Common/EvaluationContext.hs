{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
module PlutusLedgerApi.Test.Common.EvaluationContext
    ( MCostModel
    , MCekMachineCosts
    , MBuiltinCostModel
    , toMCostModel
    , extractCostModelParamsLedgerOrder
    ) where

import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusPrelude
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts

import PlutusLedgerApi.Common as Common

import Barbies
import Data.Functor.Identity
import Data.Map qualified as Map

-- A lifted cost model to `Maybe`, so we can easily clear some of its fields when extracting JSON.
type MCostModel = CostModel MCekMachineCosts MBuiltinCostModel

type MCekMachineCosts = CekMachineCostsBase Maybe

type MBuiltinCostModel = BuiltinCostModelBase MCostingFun

-- | A helper function to lift to a "full" `MCostModel`, by mapping *all* of its fields to `Just`.
-- The fields can be later on cleared, by assigning them to `Nothing`.
toMCostModel :: CostModel CekMachineCosts BuiltinCostModel
             -> MCostModel
toMCostModel cm =
   cm
   & machineCostModel
   %~ bmap (Just . runIdentity)
   & builtinCostModel
   %~ bmap (MCostingFun . Just)

{- | A variant of `extractCostModelParams` to make a mapping of params not in alphabetical order,
but in the `ParamName` order, i.e. the order expected by the ledger.

Here, overconstrained to `MCostModel`, but it could also work with `CostModel mcosts bcosts`.
-}
extractCostModelParamsLedgerOrder :: (Common.IsParamName p, Ord p)
                                  => MCostModel
                                  -> Maybe (Map.Map p Integer)
extractCostModelParamsLedgerOrder =
    extractInAlphaOrder
     >=> toLedgerOrder
    where
      extractInAlphaOrder = extractCostModelParams
      toLedgerOrder = mapKeysM readParamName

      mapKeysM :: (Monad m, Ord k2) => (k1 -> m k2) -> Map.Map k1 a -> m (Map.Map k2 a)
      mapKeysM = viaListM . mapM . firstM

      viaListM op = fmap Map.fromList . op . Map.toList
      firstM f (k,v) = (,v) <$> f k


