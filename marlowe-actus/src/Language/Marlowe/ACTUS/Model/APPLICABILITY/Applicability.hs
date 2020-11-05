{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.APPLICABILITY.Applicability where

import           Data.Maybe                                                    (isJust)
import           Data.Validation
import           Language.Marlowe.ACTUS.Definitions.ContractTerms              (ContractTerms (..), ContractType (..),
                                                                                ScheduleConfig (..),
                                                                                TermValidationError (..))
import           Language.Marlowe.ACTUS.Model.APPLICABILITY.ApplicabilityModel

validateTerms :: ContractTerms -> Validation [TermValidationError] ContractTerms
validateTerms t =
    case contractType t of
        Just PAM ->
            pure t <*
            _X (calendar . scfg) t "calendar" <*
            _X (eomc . scfg) t "end of month convention" <*
            _NN ct_NT t "notional principal" <*
            _NN_I_1 [isJust $ ct_PRD t, isJust $ ct_PPRD t] t ["purchase date", "price at purchase date"] <*
            _NN_I_1 [isJust $ ct_TD t, isJust $ ct_PTD t] t ["termination date", "price at termination"] <*
            _NN ct_MD t "maturity date"
        Just LAM ->
            pure t <*
            _X (calendar . scfg) t "calendar" <*
            _X (eomc . scfg) t "end of month convention" <*
            _NN ct_NT t "notional principal" <*
            _NN ct_IPNR t "interest rate" <*
            _NN_I_1 [isJust $ ct_PRD t, isJust $ ct_PPRD t] t ["purchase date", "price at purchase date"] <*
            _NN_I_1 [isJust $ ct_TD t, isJust $ ct_PTD t] t ["termination date", "price at termination"] <*
            _NN ct_PRCL t "principal redemption cycle" <*
            _NN_I_2 [isJust $ ct_PRNXT t, isJust $ ct_MD t] t ["periodic payment amount", "maturity date"]
        Nothing ->
            Failure [Required $ "Contract term 'contract type' is required."]
