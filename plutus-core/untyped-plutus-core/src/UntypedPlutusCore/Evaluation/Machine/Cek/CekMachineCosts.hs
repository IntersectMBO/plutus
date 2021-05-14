{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
    ( CekMachineCosts(..)
    , cekMachineCostsPrefix
    , unitCekMachineCosts
    )
where

import           PlutusCore.Evaluation.Machine.ExBudget

import qualified Data.Text                              as Text
import           Deriving.Aeson
import           Language.Haskell.TH.Syntax             (Lift)


-- | The prefix of the field names in the CekMachineCosts type, used for
-- extracting the CekMachineCosts component of the ledger's cost model
-- parameters. See Note [Cost model parameters] in CostModelInterface.
cekMachineCostsPrefix :: Text.Text
cekMachineCostsPrefix = "cek"

-- | Costs for evaluating AST nodes.  Times should be specified in picoseconds, memory sizes in bytes.

data CekMachineCosts =
    CekMachineCosts {
      cekStartupCost :: ExBudget  -- General overhead
    , cekStepCost    :: ExBudget
    }
    deriving (Eq, Show, Generic, Lift)
    deriving (FromJSON, ToJSON) via CustomJSON '[FieldLabelModifier (CamelToSnake)] CekMachineCosts

-- Charge a unit CPU cost for AST nodes: this allows us to count the number of
-- times each node type is evaluated.  For actual prediction/costing we use
-- a different version of CekMachineCosts: see ExBudgetingDefaults.defaultCekMachineCosts.
unitCekMachineCosts :: CekMachineCosts
unitCekMachineCosts =
    CekMachineCosts { cekStartupCost = zeroCost
                    , cekStepCost    = unitCost
                    }
        where
          zeroCost = ExBudget 0 0
          unitCost = ExBudget 1 0
