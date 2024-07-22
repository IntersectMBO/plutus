-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedLists #-}
module Cardano.Constitution.Validator
    ( module Export
    , validatorsWithCodes
    , validators
    , validatorCodes
    ) where

import Cardano.Constitution.Config
import Cardano.Constitution.Validator.Common as Export
import Cardano.Constitution.Validator.Sorted qualified as S
import Cardano.Constitution.Validator.Unsorted qualified as U

import Data.Map.Strict qualified as M
import PlutusTx.Code

validatorsWithCodes :: M.Map String ( ConstitutionConfig -> ConstitutionValidator
                                   , ConstitutionConfig -> CompiledCode ConstitutionValidator)
validatorsWithCodes =
    [ ("sorted", (S.mkConstitutionValidator, S.mkConstitutionCode))
    , ("unsorted", (U.mkConstitutionValidator, U.mkConstitutionCode))
    ]

validators :: M.Map String (ConstitutionConfig -> ConstitutionValidator)
validators = fmap fst validatorsWithCodes

validatorCodes :: M.Map String (ConstitutionConfig -> CompiledCode ConstitutionValidator)
validatorCodes = fmap snd validatorsWithCodes
