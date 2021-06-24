{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.Model.APPLICABILITY.Applicability where

import           Data.Maybe                                                    (isJust)
import           Data.Validation
import           Language.Marlowe.ACTUS.Definitions.ContractTerms              (CT (..), ContractTerms (..),
                                                                                ScheduleConfig (..),
                                                                                TermValidationError (..))
import           Language.Marlowe.ACTUS.Model.APPLICABILITY.ApplicabilityModel

validateTerms :: ContractTerms -> Validation [TermValidationError] ContractTerms
validateTerms t =
    case contractType t of
        PAM ->
            pure t <*
            _NN ct_IED t "initial exchange date" <*
            _NN ct_DCC t "day count convention" <*
            _X (calendar . scfg) t "calendar" <*
            _X (bdc . scfg) t "business day convention" <*
            _X (eomc . scfg) t "end of month convention" <*
            _X_I_2 (ct_FER t) [isJust $ ct_FEANX t, isJust $ ct_FECL t] t "fee rate" ["cycle anchor date of fee", "cycle of fee"] <*
            _X ct_FEAC t "fee accrued" <*
            _NN_I_1 [isJust $ ct_FEB t, isJust $ ct_FER t] t ["fee basis", "fee rate"] <*
            _NN ct_IPNR t "nominal interest rate" <*
            _X ct_IPAC t "accrued interest" <*
            _X ct_IPCED t "capitalization end date" <*
            _X ct_PDIED t "premium discount at IED" <*
            _X_I_2 (ct_SCEF t) [isJust $ ct_SCANX t, isJust $ ct_SCCL t] t "scaling effect" ["cycle anchor date of scaling index", "cycle of scaling index"] <*
            _X_I_1 [isJust $ ct_RRCL t, isJust $ ct_RRANX t]
              (map (\x -> isJust $ x t) [ct_RRNXT, ct_RRSP, ct_RRMLT, ct_RRPF, ct_RRPC, ct_RRLC, ct_RRLF]) t
              ["cycle anchor date of rate reset", "cycle of rate reset"]
              [ "next reset rate", "rate spread", "rate multiplier", "period floor", "period cap", "life cap", "life floor"] <*
            _NN ct_NT t "notional principal" <*
            _NN_I_1 [isJust $ ct_PRD t, isJust $ ct_PPRD t] t ["purchase date", "price at purchase date"] <*
            _NN_I_1 [isJust $ ct_TD t, isJust $ ct_PTD t] t ["termination date", "price at termination"] <*
            _NN ct_MD t "maturity date" <*
            _NN_I_1 [isJust $ ct_SCEF t, isJust $ ct_SCIED t, isJust $ ct_SCCDD t] t ["scaling effect", "scaling index at status date", "scaling index at contract deal date"] <*
            _X_I_1 [isJust $ ct_PYRT t, isJust $ ct_PYTP t] [isJust $ ct_PPEF t] t ["penalty rate", "penalty type"] ["prepayment effect"]
        LAM ->
            pure t <*
            _NN ct_IED t "initial exchange date" <*
            _NN ct_DCC t "day count convention" <*
            _X (calendar . scfg) t "calendar" <*
            _X (bdc . scfg) t "business day convention" <*
            _X (eomc . scfg) t "end of month convention" <*
            _X_I_4 [isJust $ ct_IPCBCL t, isJust $ ct_IPCBANX t] t ["cycle of interest calculation base", "cycle anchor date of interest calculation base"] <*
            _X ct_FEAC t "fee accrued" <*
            _NN_I_1 [isJust $ ct_FEB t, isJust $ ct_FER t] t ["fee basis", "fee rate"] <*
            _NN ct_IPNR t "nominal interest rate" <*
            _X ct_IPAC t "accrued interest" <*
            _X ct_IPCED t "capitalization end date" <*
            _X ct_PDIED t "premium discount at IED" <*
            _NN_I_3 ct_IPCBA t "interest calculation base amount" <*
            _X_I_1 [isJust $ ct_RRCL t, isJust $ ct_RRANX t]
              (map (\x -> isJust $ x t) [ct_RRNXT, ct_RRSP, ct_RRMLT, ct_RRPF, ct_RRPC, ct_RRLC, ct_RRLF]) t
              ["cycle anchor date of rate reset", "cycle of rate reset"]
              [ "next reset rate", "rate spread", "rate multiplier", "period floor", "period cap", "life cap", "life floor"] <*
            _NN ct_NT t "notional principal" <*
            _NN_I_1 [isJust $ ct_PRD t, isJust $ ct_PPRD t] t ["purchase date", "price at purchase date"] <*
            _NN_I_1 [isJust $ ct_TD t, isJust $ ct_PTD t] t ["termination date", "price at termination"] <*
            _NN ct_PRCL t "principal redemption cycle" <*
            _X ct_MD t "maturity date" <*
            _X ct_PRNXT t "periodic payment amount" <*
            _NN_I_1 [isJust $ ct_SCEF t, isJust $ ct_SCIED t, isJust $ ct_SCCDD t] t ["scaling effect", "scaling index at status date", "scaling index at contract deal date"] <*
            _X_I_1 [isJust $ ct_PYRT t, isJust $ ct_PYTP t] [isJust $ ct_PPEF t] t ["penalty rate", "penalty type"] ["prepayment effect"]
        NAM ->
            pure t <*
            _NN ct_IED t "initial exchange date" <*
            _NN ct_DCC t "day count convention" <*
            _X (calendar . scfg) t "calendar" <*
            _X (bdc . scfg) t "business day convention" <*
            _X (eomc . scfg) t "end of month convention" <*
            _X_I_4 [isJust $ ct_IPCBCL t, isJust $ ct_IPCBANX t] t ["cycle of interest calculation base", "cycle anchor date of interest calculation base"] <*
            _X ct_FEAC t "fee accrued" <*
            _NN_I_1 [isJust $ ct_FEB t, isJust $ ct_FER t] t ["fee basis", "fee rate"] <*
            _NN ct_IPNR t "nominal interest rate" <*
            _X ct_IPAC t "accrued interest" <*
            _X ct_IPCED t "capitalization end date" <*
            _X ct_PDIED t "premium discount at IED" <*
            _X ct_IPCL t "cycle of interest payment" <*
            _X ct_IPANX t "cycle anchor date of interest payment" <*
            _NN_I_3 ct_IPCBA t "interest calculation base amount" <*
            _X_I_1 [isJust $ ct_RRCL t, isJust $ ct_RRANX t]
              (map (\x -> isJust $ x t) [ct_RRNXT, ct_RRSP, ct_RRMLT, ct_RRPF, ct_RRPC, ct_RRLC, ct_RRLF]) t
              ["cycle anchor date of rate reset", "cycle of rate reset"]
              [ "next reset rate", "rate spread", "rate multiplier", "period floor", "period cap", "life cap", "life floor"] <*
            _NN ct_NT t "notional principal" <*
            _NN_I_1 [isJust $ ct_PRD t, isJust $ ct_PPRD t] t ["purchase date", "price at purchase date"] <*
            _NN_I_1 [isJust $ ct_TD t, isJust $ ct_PTD t] t ["termination date", "price at termination"] <*
            _NN ct_PRCL t "principal redemption cycle" <*
            _X ct_MD t "maturity date" <*
            _NN ct_PRNXT t "periodic payment amount" <*
            _NN_I_1 [isJust $ ct_SCEF t, isJust $ ct_SCIED t, isJust $ ct_SCCDD t] t ["scaling effect", "scaling index at status date", "scaling index at contract deal date"] <*
            _X_I_1 [isJust $ ct_PYRT t, isJust $ ct_PYTP t] [isJust $ ct_PPEF t] t ["penalty rate", "penalty type"] ["prepayment effect"]
