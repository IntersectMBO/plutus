{-# LANGUAGE RecordWildCards #-}

{- This module contains templates for Marlowe constructs required by ACTUS logic -}
module Language.Marlowe.ACTUS.ControlLp
    ( lpValidator
    , genLpContract
    , genStaticContract
    , genFsContract
    )
where

import           Ledger                     (Slot (..))
import Language.Marlowe.ACTUS.STF.StateTransitionLp
    ( stateTransitionLp )
import Language.Marlowe.ACTUS.POF.PayoffLp ( payoffLp )
import Language.Marlowe.ACTUS.STF.StateTransitionLp
    ( stateTransitionLp )
import Language.Marlowe.ACTUS.STF.StateTransitionFs
    ( stateTransitionFs )
import Language.Marlowe.ACTUS.INIT.StateInitializationFs
    ( inititializeStateFs )
import Language.Marlowe.ACTUS.POF.PayoffFs ( payoffFs )
import Language.Marlowe.ACTUS.Control ( invoice, inquiry, inquiryFs )
import Language.Marlowe.ACTUS.Ops ( dayToSlotNumber )
import Language.Marlowe.ACTUS.Schedule
    ( CashFlow(CashFlow, currency, amount, cashEvent,
               cashCalculationDay, cashPaymentDay, cashCounterParty, cashParty,
               cashContractId, tick) )
import Language.Marlowe.ACTUS.ProjectedCashFlows
    ( genProjectedCashflows )
import Language.Marlowe.ACTUS.BusinessEvents
    ( mapEventType, )
import Language.Marlowe.ACTUS.ContractTerms ( ContractTerms )
import Data.String ( IsString(fromString) )
import Data.List (zip4)
import Language.Marlowe
    ( Contract(Close, If, Let),
      Observation(ValueEQ),
      Value(Constant, UseValue, NegValue),
      ValueId(..),
      Slot(Slot) )


expectedPayoffAt :: Integer -> ValueId
expectedPayoffAt t = ValueId $ fromString $ "expected-payoff_" ++ show t

payoffAt :: Integer -> ValueId
payoffAt t = ValueId $ fromString $ "payoff_" ++ show t

lpValidator :: Integer -> Contract -> Contract
lpValidator t continue =
    let payoffOk = ValueEQ (UseValue $ expectedPayoffAt t)
                           (UseValue $ payoffAt t)
        --todo dateOk 
        --todo check that previous events happened
    in  (If payoffOk continue Close)

genLpContract :: ContractTerms -> Integer -> Contract -> Contract
genLpContract terms t continue =
    --todo: state initialization
    inquiry (show t) "party" 0 "oracle"
        $ stateTransitionLp terms t
        $ Let (expectedPayoffAt t) (payoffLp terms t)
        $ lpValidator t
        $ invoice "party" "counterparty" (UseValue $ payoffAt t) 1000000
        continue

genStaticContract :: ContractTerms -> Contract
genStaticContract terms = 
    let
        cfs = genProjectedCashflows terms
        gen CashFlow{..} = invoice "party" "counterparty" (Constant $ round amount) (Slot $ dayToSlotNumber cashPaymentDay)
    in foldl (flip gen) Close cfs


genFsContract :: ContractTerms -> Contract
genFsContract terms = 
    let
        schedCfs = genProjectedCashflows terms
        schedEvents = mapEventType . cashEvent <$> schedCfs
        schedDates = Slot . dayToSlotNumber . cashPaymentDay <$> schedCfs
        cfsDirections = amount <$> schedCfs
        gen (ev, date, r, t) cont = inquiryFs ev ("_" ++ show t) date "oracle"
            $ stateTransitionFs ev terms t
            $ Let (payoffAt t) (payoffFs ev terms t)
            $ if r > 0.0    then invoice "party" "counterparty" (UseValue $ payoffAt t) date cont
                            else invoice "counterparty" "party" (NegValue $ UseValue $ payoffAt t) date cont
        schedule = foldl (flip gen) Close $ reverse $ zip4 schedEvents schedDates cfsDirections [1..]
    in inititializeStateFs terms schedule
