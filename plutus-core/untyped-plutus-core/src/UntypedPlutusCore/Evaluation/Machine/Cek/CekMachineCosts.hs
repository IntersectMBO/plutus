-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UndecidableInstances #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
  ( CekMachineCosts
  , CekMachineCostsBase (..)
  , cekMachineCostsPrefix
  , unitCekMachineCosts
  )
where

import PlutusCore.Evaluation.Machine.ExBudget

import Barbies
import Control.DeepSeq
import Data.Functor.Identity
import Data.Text qualified as Text
import Deriving.Aeson
import Language.Haskell.TH.Syntax (Lift)
import NoThunks.Class

{-| The prefix of the field names in the CekMachineCosts type, used for
extracting the CekMachineCosts component of the ledger's cost model
parameters. See Note [Cost model parameters] in CostModelInterface. -}
cekMachineCostsPrefix :: Text.Text
cekMachineCostsPrefix = "cek"

-- | Costs for evaluating AST nodes.  Times should be specified in picoseconds, memory sizes in bytes.
type CekMachineCosts = CekMachineCostsBase Identity

data CekMachineCostsBase f
  = CekMachineCostsBase
  { cekStartupCost :: f ExBudget -- General overhead
  , cekVarCost :: f ExBudget
  , cekConstCost :: f ExBudget
  , cekLamCost :: f ExBudget
  , cekDelayCost :: f ExBudget
  , cekForceCost :: f ExBudget
  , cekApplyCost :: f ExBudget
  , cekBuiltinCost :: f ExBudget
  {-^ Just the cost of evaluating a Builtin node, not the builtin itself.
  There's no entry for Error since we'll be exiting anyway; also, what would
  happen if calling 'Error' caused the budget to be exceeded? -}
  , cekConstrCost :: f ExBudget
  , cekCaseCost :: f ExBudget
  , cekMatchCost :: f ExBudget
  {-^ Fixed cost of entering a 'Match' node. This is separate from 'cekPatternCost' so repeated
  shallow matches remain bounded without making wide structural matching more expensive than the
  equivalent builtin program. -}
  , cekPatternCost :: f ExBudget
  {-^ Cost of cheap, incrementally spent Match work: an alternative/root probe, one compared
  64-bit bytestring word, or one unit of reached-capture work. Each reached capture spends two
  units before retention: one for its eventual strict spine cell and one for its implicit handler
  application. -}
  , cekPatternStructuralCost :: f ExBudget
  {-^ Cost of one reached Match child/field edge, including dispatch of that child and the bounded
  exact-arity probe at the edge. It is separate because direct affordability spending plus
  structural traversal is materially more expensive than scalar work. -}
  , cekPatternFailureCost :: f ExBudget
  {-^ Cost of abandoning a known-failed alternative, advancing, and probing the next ordered
  alternative. The work that discovers the mismatch is covered by its preceding base or structural
  charge; this cost is spent before the transition and next probe. There is no pattern pre-scan,
  cached measure, or refund. Reached captures retain their earlier materialization/application
  charge even when later work abandons the alternative. -}
  }
  deriving stock (Generic)
  deriving anyclass (FunctorB, TraversableB, ConstraintsB)

deriving via
  CustomJSON
    '[FieldLabelModifier LowerInitialCharacter]
    (CekMachineCostsBase Identity)
  instance
    ToJSON (CekMachineCostsBase Identity)
deriving via
  CustomJSON
    '[FieldLabelModifier LowerInitialCharacter]
    (CekMachineCostsBase Identity)
  instance
    FromJSON (CekMachineCostsBase Identity)

-- This instance will omit the generation of JSON for Nothing fields,
-- (any functors which have Maybe functor at the outer layer)
deriving via
  CustomJSON
    '[OmitNothingFields, FieldLabelModifier LowerInitialCharacter]
    (CekMachineCostsBase Maybe)
  instance
    ToJSON (CekMachineCostsBase Maybe)

deriving stock instance AllBF Show f CekMachineCostsBase => Show (CekMachineCostsBase f)
deriving stock instance AllBF Eq f CekMachineCostsBase => Eq (CekMachineCostsBase f)
deriving stock instance AllBF Lift f CekMachineCostsBase => Lift (CekMachineCostsBase f)
deriving anyclass instance AllBF NFData f CekMachineCostsBase => NFData (CekMachineCostsBase f)
deriving anyclass instance AllBF NoThunks f CekMachineCostsBase => NoThunks (CekMachineCostsBase f)

-- Charge a unit CPU cost for AST nodes: this allows us to count the number of
-- times each node type is evaluated.  For actual prediction/costing we use
-- a different version of CekMachineCosts: see ExBudgetingDefaults.defaultCekMachineCosts.
unitCekMachineCosts :: CekMachineCosts
unitCekMachineCosts =
  CekMachineCostsBase
    { cekStartupCost = zeroCost
    , cekVarCost = unitCost
    , cekConstCost = unitCost
    , cekLamCost = unitCost
    , cekDelayCost = unitCost
    , cekForceCost = unitCost
    , cekApplyCost = unitCost
    , cekBuiltinCost = unitCost
    , cekConstrCost = unitCost
    , cekCaseCost = unitCost
    , cekMatchCost = unitCost
    , cekPatternCost = unitCost
    , cekPatternStructuralCost = unitCost
    , cekPatternFailureCost = unitCost
    }
  where
    zeroCost = Identity $ ExBudget 0 0
    unitCost = Identity $ ExBudget 1 0
