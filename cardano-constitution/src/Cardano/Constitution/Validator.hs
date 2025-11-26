-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedLists #-}

module Cardano.Constitution.Validator
  ( module Export
  , defaultValidators
  , defaultValidatorsWithCodes
  ) where

import Cardano.Constitution.Validator.Common as Export
import Cardano.Constitution.Validator.Sorted qualified as S
import Cardano.Constitution.Validator.Unsorted qualified as U

-- import Cardano.Constitution.Validator.Reference.Script qualified as R

import Data.Map.Strict qualified as M
import PlutusTx.Code

defaultValidatorsWithCodes :: M.Map String (ConstitutionValidator, CompiledCode ConstitutionValidator)
defaultValidatorsWithCodes =
  [ ("sorted", (S.defaultConstitutionValidator, S.defaultConstitutionCode))
  , ("unsorted", (U.defaultConstitutionValidator, U.defaultConstitutionCode))
  -- Disabled, 7 tests fail
  -- , ("ref", (R.constitutionScript, R.compiledConstitutionScript))
  ]

defaultValidators :: M.Map String ConstitutionValidator
defaultValidators = fmap fst defaultValidatorsWithCodes
