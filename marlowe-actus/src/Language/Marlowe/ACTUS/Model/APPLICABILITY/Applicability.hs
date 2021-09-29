{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.APPLICABILITY.Applicability where

import           Data.Maybe                                                    (isJust)
import           Data.Validation
import           Language.Marlowe.ACTUS.Definitions.ContractTerms              (CT (..), ContractTerms,
                                                                                ContractTermsPoly (..),
                                                                                ScheduleConfig (..),
                                                                                TermValidationError (..))
import           Language.Marlowe.ACTUS.Model.APPLICABILITY.ApplicabilityModel

validateTerms :: ContractTerms -> Validation [TermValidationError] ContractTerms
validateTerms ct@ContractTermsPoly {contractType = PAM, ..} =
  ct
    <$ _NN ct_IED ct "initial exchange date"
    <* _NN ct_DCC ct "day count convention"
    <* _X (calendar scfg) ct "calendar"
    <* _X (bdc scfg) ct "business day convention"
    <* _X (eomc scfg) ct "end of month convention"
    <* _X_I_2 ct_FER [isJust ct_FEANX, isJust ct_FECL] ct "fee rate" ["cycle anchor date of fee", "cycle of fee"]
    <* _X ct_FEAC ct "fee accrued"
    <* _NN_I_1 [isJust ct_FEB, isJust ct_FER] ct ["fee basis", "fee rate"]
    <* _NN ct_IPNR ct "nominal interest rate"
    <* _X ct_IPAC ct "accrued interest"
    <* _X ct_IPCED ct "capitalization end date"
    <* _X ct_PDIED ct "premium discount at IED"
    <* _X_I_2 ct_SCEF [isJust ct_SCANX, isJust ct_SCCL] ct "scaling effect" ["cycle anchor date of scaling index", "cycle of scaling index"]
    <* _X_I_1
      [isJust ct_RRCL, isJust ct_RRANX]
      [isJust ct_RRNXT, isJust ct_RRSP, isJust ct_RRMLT, isJust ct_RRPF, isJust ct_RRPC, isJust ct_RRLC, isJust ct_RRLF]
      ct
      ["cycle anchor date of rate reset", "cycle of rate reset"]
      ["next reset rate", "rate spread", "rate multiplier", "period floor", "period cap", "life cap", "life floor"]
    <* _NN ct_NT ct "notional principal"
    <* _NN_I_1 [isJust ct_PRD, isJust ct_PPRD] ct ["purchase date", "price at purchase date"]
    <* _NN_I_1 [isJust ct_TD, isJust ct_PTD] ct ["termination date", "price at termination"]
    <* _NN ct_MD ct "maturity date"
    <* _NN_I_1 [isJust ct_SCEF, isJust ct_SCIED, isJust ct_SCCDD] ct ["scaling effect", "scaling index at status date", "scaling index at contract deal date"]
    <* _X_I_1 [isJust ct_PYRT, isJust ct_PYTP] [isJust ct_PPEF] ct ["penalty rate", "penalty type"] ["prepayment effect"]

validateTerms ct@ContractTermsPoly {contractType = LAM, ..} =
  ct
    <$ _NN ct_IED ct "initial exchange date"
    <* _NN ct_DCC ct "day count convention"
    <* _X (calendar scfg) ct "calendar"
    <* _X (bdc scfg) ct "business day convention"
    <* _X (eomc scfg) ct "end of month convention"
    <* _X_I_4 [isJust ct_IPCBCL, isJust ct_IPCBANX] ct ["cycle of interest calculation base", "cycle anchor date of interest calculation base"]
    <* _X ct_FEAC ct "fee accrued"
    <* _NN_I_1 [isJust ct_FEB, isJust ct_FER] ct ["fee basis", "fee rate"]
    <* _NN ct_IPNR ct "nominal interest rate"
    <* _X ct_IPAC ct "accrued interest"
    <* _X ct_IPCED ct "capitalization end date"
    <* _X ct_PDIED ct "premium discount at IED"
    <* _NN_I_3 ct_IPCBA ct "interest calculation base amount"
    <* _X_I_1
      [isJust ct_RRCL, isJust ct_RRANX]
      [isJust ct_RRNXT, isJust ct_RRSP, isJust ct_RRMLT, isJust ct_RRPF, isJust ct_RRPC, isJust ct_RRLC, isJust ct_RRLF]
      ct
      ["cycle anchor date of rate reset", "cycle of rate reset"]
      ["next reset rate", "rate spread", "rate multiplier", "period floor", "period cap", "life cap", "life floor"]
    <* _NN ct_NT ct "notional principal"
    <* _NN_I_1 [isJust ct_PRD, isJust ct_PPRD] ct ["purchase date", "price at purchase date"]
    <* _NN_I_1 [isJust ct_TD, isJust ct_PTD] ct ["termination date", "price at termination"]
    <* _NN ct_PRCL ct "principal redemption cycle"
    <* _X ct_MD ct "maturity date"
    <* _X ct_PRNXT ct "periodic payment amount"
    <* _NN_I_1 [isJust ct_SCEF, isJust ct_SCIED, isJust ct_SCCDD] ct ["scaling effect", "scaling index at status date", "scaling index at contract deal date"]
    <* _X_I_1 [isJust ct_PYRT, isJust ct_PYTP] [isJust ct_PPEF] ct ["penalty rate", "penalty type"] ["prepayment effect"]

validateTerms ct@ContractTermsPoly {contractType = NAM, ..} =
  ct
    <$ _NN ct_IED ct "initial exchange date"
    <* _NN ct_DCC ct "day count convention"
    <* _X (calendar scfg) ct "calendar"
    <* _X (bdc scfg) ct "business day convention"
    <* _X (eomc scfg) ct "end of month convention"
    <* _X_I_4 [isJust ct_IPCBCL, isJust ct_IPCBANX] ct ["cycle of interest calculation base", "cycle anchor date of interest calculation base"]
    <* _X ct_FEAC ct "fee accrued"
    <* _NN_I_1 [isJust ct_FEB, isJust ct_FER] ct ["fee basis", "fee rate"]
    <* _NN ct_IPNR ct "nominal interest rate"
    <* _X ct_IPAC ct "accrued interest"
    <* _X ct_IPCED ct "capitalization end date"
    <* _X ct_PDIED ct "premium discount at IED"
    <* _X ct_IPCL ct "cycle of interest payment"
    <* _X ct_IPANX ct "cycle anchor date of interest payment"
    <* _NN_I_3 ct_IPCBA ct "interest calculation base amount"
    <* _X_I_1
      [isJust ct_RRCL, isJust ct_RRANX]
      [isJust ct_RRNXT, isJust ct_RRSP, isJust ct_RRMLT, isJust ct_RRPF, isJust ct_RRPC, isJust ct_RRLC, isJust ct_RRLF]
      ct
      ["cycle anchor date of rate reset", "cycle of rate reset"]
      ["next reset rate", "rate spread", "rate multiplier", "period floor", "period cap", "life cap", "life floor"]
    <* _NN ct_NT ct "notional principal"
    <* _NN_I_1 [isJust ct_PRD, isJust ct_PPRD] ct ["purchase date", "price at purchase date"]
    <* _NN_I_1 [isJust ct_TD, isJust ct_PTD] ct ["termination date", "price at termination"]
    <* _NN ct_PRCL ct "principal redemption cycle"
    <* _X ct_MD ct "maturity date"
    <* _NN ct_PRNXT ct "periodic payment amount"
    <* _NN_I_1 [isJust ct_SCEF, isJust ct_SCIED, isJust ct_SCCDD] ct ["scaling effect", "scaling index at status date", "scaling index at contract deal date"]
    <* _X_I_1 [isJust ct_PYRT, isJust ct_PYTP] [isJust ct_PPEF] ct ["penalty rate", "penalty type"] ["prepayment effect"]

validateTerms ct@ContractTermsPoly {contractType = ANN, ..} =
  ct
    <$ _NN ct_IED ct "initial exchange date"
    <* _NN ct_DCC ct "day count convention"
    <* _X (calendar scfg) ct "calendar"
    <* _X (bdc scfg) ct "business day convention"
    <* _X (eomc scfg) ct "end of month convention"
    <* _X_I_4 [isJust ct_IPCBCL, isJust ct_IPCBANX] ct ["cycle of interest calculation base", "cycle anchor date of interest calculation base"]
    <* _X ct_FEAC ct "fee accrued"
    <* _NN_I_1 [isJust ct_FEB, isJust ct_FER] ct ["fee basis", "fee rate"]
    <* _NN ct_IPNR ct "nominal interest rate"
    <* _X ct_IPAC ct "accrued interest"
    <* _X ct_IPCED ct "capitalization end date"
    <* _X ct_PDIED ct "premium discount at IED"
    <* _X ct_IPCL ct "cycle of interest payment"
    <* _X ct_IPANX ct "cycle anchor date of interest payment"
    <* _NN_I_3 ct_IPCBA ct "interest calculation base amount"
    <* _X_I_1
      [isJust ct_RRCL, isJust ct_RRANX]
      [isJust ct_RRNXT, isJust ct_RRSP, isJust ct_RRMLT, isJust ct_RRPF, isJust ct_RRPC, isJust ct_RRLC, isJust ct_RRLF]
      ct
      ["cycle anchor date of rate reset", "cycle of rate reset"]
      ["next reset rate", "rate spread", "rate multiplier", "period floor", "period cap", "life cap", "life floor"]
    <* _NN ct_NT ct "notional principal"
    <* _NN_I_1 [isJust ct_PRD, isJust ct_PPRD] ct ["purchase date", "price at purchase date"]
    <* _NN_I_1 [isJust ct_TD, isJust ct_PTD] ct ["termination date", "price at termination"]
    <* _NN ct_PRCL ct "principal redemption cycle"
    <* _X ct_MD ct "maturity date"
    <* _NN ct_PRNXT ct "periodic payment amount"
    <* _NN_I_1 [isJust ct_SCEF, isJust ct_SCIED, isJust ct_SCCDD] ct ["scaling effect", "scaling index at status date", "scaling index at contract deal date"]
    <* _X_I_1 [isJust ct_PYRT, isJust ct_PYTP] [isJust ct_PPEF] ct ["penalty rate", "penalty type"] ["prepayment effect"]

