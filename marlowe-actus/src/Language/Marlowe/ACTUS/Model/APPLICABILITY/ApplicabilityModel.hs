{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Language.Marlowe.ACTUS.Model.APPLICABILITY.ApplicabilityModel where

import           Data.Maybe                                       ()
import           Data.Validation                                  (Validation (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (ContractTerms (..), TermValidationError (..))

-- Applicability Validation Functions

-- optional
_X _ t _ = Success t

-- non-nullable / required
_NN _ct t@ContractTerms{..} termName =
    case _ct t of
        Just _ -> Success t
        Nothing -> Failure [Required $ "Contract term '" ++ termName ++ "' is required for contract type '" ++ show contractType ++ "'"]

-- not applicable
_NA _ct t@ContractTerms{..} termName =
    case _ct t of
        Just _ -> Failure [NotApplicable $ "Contract term '" ++ termName ++ "' is not applicable for contract type '" ++ show contractType ++ "'"]
        Nothing -> Success t

-- NN(I, 1, _) (If one is defined, all must be defined)
_NN_I_1 _cts t@ContractTerms{..} termNames =
    case all id _cts of
        False -> if any id _cts then
                    Failure [Required $ "All contract terms in group " ++ show termNames ++ " should be defined if one of them is defined for contract type '" ++ show contractType ++ "'"]
                else
                    Success t
        True -> Success t

-- NN(I, 2, _) (At least one must be defined)
_NN_I_2 _cts t@ContractTerms{..} termNames =
    case any id _cts of
        False -> Failure [Required $ "At least one contract term in group " ++ show termNames ++ " should be defined for contract type '" ++ show contractType ++ "'"]
        True -> Success t
