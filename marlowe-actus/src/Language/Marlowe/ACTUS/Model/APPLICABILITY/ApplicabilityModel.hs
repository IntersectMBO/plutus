{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Language.Marlowe.ACTUS.Model.APPLICABILITY.ApplicabilityModel where

import           Data.Maybe                                       (fromJust)
import           Data.Validation                                  (Validation (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (ContractTerms (..), IPCB (IPCB_NTIED, IPCB_NTL),
                                                                   TermValidationError (..))

-- Applicability Validation Functions

-- optional
_X _ t _ = Success t

-- The conditional term with c=1 is optional when any of the unconditional terms with c=0 is defined.
_X_I_1 _uncondCts _condCt t@ContractTerms{..} uncondNames condName =
    case any id _uncondCts of
        True ->
            Success t
        False ->
            case _condCt t of
                Just _ ->
                    Failure [Required $ "The unconditional terms " ++ show uncondNames ++ " must be defined when " ++ condName ++ " is defined for contract type '" ++ show (fromJust contractType) ++ "'"]
                Nothing ->
                    Success t

-- If the unconditional term with c=0 in the group is defined, then at least one of the conditional terms with c=2 must be defined.
_X_I_2 _uncondCt _condCts  t@ContractTerms{..} uncondName condNames =
    case _uncondCt t of
        Just _ ->
            case any id _condCts of
                True ->
                    Success t
                False ->
                    Failure [Required $ "At least one of the conditional terms in group " ++ show condNames ++ " must be defined when " ++ uncondName ++ " is defined for contract type '" ++ show (fromJust contractType) ++ "'"]
        Nothing -> Success t

_X_I_4 _condCts  t@ContractTerms{..} condNames =
    case ct_IPCB of
        Just IPCB_NTL ->
            case any id _condCts of
                True ->
                    Success t
                False ->
                    Failure [Required $ "At least one of the conditional terms in group " ++ show condNames ++ " must be defined when interest calculation base is NTL for contract type '" ++ show (fromJust contractType) ++ "'"]
        _ -> Success t


-- non-nullable / required
_NN _ct t@ContractTerms{..} termName =
    case _ct t of
        Just _ -> Success t
        Nothing -> Failure [Required $ "Contract term '" ++ termName ++ "' is required for contract type '" ++ show (fromJust contractType) ++ "'"]

-- not applicable
_NA _ct t@ContractTerms{..} termName =
    case _ct t of
        Just _ -> Failure [NotApplicable $ "Contract term '" ++ termName ++ "' is not applicable for contract type '" ++ show (fromJust contractType) ++ "'"]
        Nothing -> Success t

-- NN(I, 1, _) (If one is defined, all must be defined)
_NN_I_1 _cts t@ContractTerms{..} termNames =
    case all id _cts of
        False -> if any id _cts then
                    Failure [Required $ "All contract terms in group " ++ show termNames ++ " should be defined if one of them is defined for contract type '" ++ show (fromJust contractType) ++ "'"]
                else
                    Success t
        True -> Success t

-- NN(I, 2, _) (At least one must be defined)
_NN_I_2 _cts t@ContractTerms{..} termNames =
    case any id _cts of
        False -> Failure [Required $ "At least one contract term in group " ++ show termNames ++ " should be defined for contract type '" ++ show (fromJust contractType) ++ "'"]
        True -> Success t

_NN_I_3 _ct t@ContractTerms{..} termName =
    case ct_IPCB of
        Just IPCB_NTIED ->
          case _ct t of
            Just _ -> Success t
            Nothing -> Failure [Required $ "Contract term " ++ termName ++ " must be defined when interest calculation base is NTIED"]
        _ ->
            Success t
