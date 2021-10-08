{-# LANGUAGE RecordWildCards #-}

{-| = ACTUS Generator

Given ACTUS contract terms a Marlowe contract is generated. There are two different functions
for generating the contracts:

* For 'genStaticContract' the risk factors are all known at contract creation
* In 'genFsContract' risk factors are added to the Marlowe contract, i.e. will
  be observed during the life time of the contract

-}

module Language.Marlowe.ACTUS.Generator
  (   genStaticContract
    , genFsContract
  )
where

import           Control.Monad.Reader
import           Data.Foldable                                              (foldrM)
import qualified Data.List                                                  as L (foldl', zip5)
import           Data.Maybe                                                 (maybeToList)
import           Data.Monoid                                                (Endo (Endo, appEndo))
import           Data.String                                                (IsString (fromString))
import           Data.Time                                                  (LocalTime)
import           Data.Validation                                            (Validation (..))
import           Language.Marlowe                                           (Action (..), Bound (..), Case (..),
                                                                             ChoiceId (..), Contract (..),
                                                                             Observation (..), Party (..), Payee (..),
                                                                             Slot (..), Value (..), ValueId (ValueId),
                                                                             ada)
import           Language.Marlowe.ACTUS.Analysis                            (genProjectedCashflows)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (..), RiskFactors,
                                                                             RiskFactorsMarlowe, RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractState, ContractStateMarlowe,
                                                                             ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (Assertion (..), AssertionContext (..),
                                                                             Assertions (..), ContractTerms,
                                                                             ContractTermsPoly (..),
                                                                             TermValidationError (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule                (CashFlow (..), ShiftedDay (..),
                                                                             calculationDay)
import           Language.Marlowe.ACTUS.MarloweCompat                       (constnt, letval, marloweTime,
                                                                             timeToSlotNumber, toMarloweFixedPoint,
                                                                             useval)
import           Language.Marlowe.ACTUS.Model.APPLICABILITY.Applicability   (validateTerms)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (initializeState)
import           Language.Marlowe.ACTUS.Model.POF.PayoffFs                  (payoffFs)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule        (schedule)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule        as S (maturity)
import           Language.Marlowe.ACTUS.Model.STF.StateTransition           (CtxSTF (..))
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionFs         (stateTransition)
import           Language.Marlowe.ACTUS.Ops                                 as O (ActusNum (..), YearFractionOps (_y))
import           Ledger.Value                                               (TokenName (TokenName))
import           Prelude                                                    as P hiding (Fractional, Num, (*), (+), (/))

-- |'genStaticContract' validates the contract terms in order to generate a
-- Marlowe contract with risk factors known in advance. The contract therefore
-- only consists of transactions, i.e. 'Deposit' and 'Pay'
genStaticContract ::
     ContractTerms                             -- ^ ACTUS contract terms
  -> Validation [TermValidationError] Contract -- ^ Marlowe contract or applicability errors
genStaticContract = fmap genStaticContract' . validateTerms

genStaticContract' :: ContractTerms -> Contract
genStaticContract' ct =
  let cfs = genProjectedCashflows defaultRiskFactors ct
      gen CashFlow {..}
        | amount == 0.0 = id
        | amount > 0.0 =
          invoice
            "party"
            "counterparty"
            (Constant $ round amount)
            (Slot $ timeToSlotNumber cashPaymentDay)
        | otherwise =
          invoice
            "counterparty"
            "party"
            (Constant $ round $ - amount)
            (Slot $ timeToSlotNumber cashPaymentDay)
   in L.foldl' (flip gen) Close $ reverse cfs

invoice :: String -> String -> Value Observation -> Slot -> Contract -> Contract
invoice from to amount timeout continue =
  let party = Role $ TokenName $ fromString from
      counterparty = Role $ TokenName $ fromString to
   in When
        [ Case
            (Deposit party party ada amount)
            ( Pay
                party
                (Party counterparty)
                ada
                amount
                continue
            )
        ]
        timeout
        Close

defaultRiskFactors :: EventType -> LocalTime -> RiskFactors
defaultRiskFactors _ _ =
  RiskFactorsPoly
    { o_rf_CURS = 1.0,
      o_rf_RRMO = 1.0,
      o_rf_SCMO = 1.0,
      pp_payoff = 0.0
    }

-- |'genFsContract' validatate the applicabilty of the contract terms in order
-- to genereate a Marlowe contract with risk factors observed at a given point
-- in time
genFsContract ::
     ContractTerms                             -- ^ ACTUS contract terms
  -> Validation [TermValidationError] Contract -- ^ Marlowe contract or applicabilty errors
genFsContract = fmap genFsContract' . validateTerms

genFsContract' :: ContractTerms -> Contract
genFsContract' ct =
  let projectedCashflows = genProjectedCashflows defaultRiskFactors ct
      eventTypesOfCashflows = cashEvent <$> projectedCashflows
      paymentDayCashflows = Slot . timeToSlotNumber . cashPaymentDay <$> projectedCashflows
      previousDates = ct_SD ct : (cashCalculationDay <$> projectedCashflows)

      gen :: (CashFlow, LocalTime, EventType, Slot, Integer) -> Contract -> Reader (CtxSTF Double LocalTime) Contract
      gen (cf, prevDate, ev, date, i) cont =
        let payoffAt :: Show a => a -> ValueId
            payoffAt t = ValueId $ fromString $ "payoff_" ++ show t

            calcDate :: LocalTime
            calcDate = cashCalculationDay cf

            stateToContract :: ContractStateMarlowe -> Contract -> Contract
            stateToContract ContractStatePoly {..} =
              letval "tmd" i tmd
                . letval "nt" i nt
                . letval "ipnr" i ipnr
                . letval "ipac" i ipac
                . letval "feac" i feac
                . letval "nsc" i nsc
                . letval "isc" i isc
                . letval "sd" i sd
                . letval "prnxt" i prnxt
                . letval "ipcb" i ipcb

            comment :: EventType -> Contract -> Contract
            comment IED = letval "IED" i (constnt 0)
            comment MD  = letval "MD" i (constnt 0)
            comment IP  = letval ("IP:" ++ show calcDate ++ show prevDate) i (constnt 0)
            comment RR  = letval ("RR:" ++ show calcDate) i (constnt 0)
            comment FP  = letval ("FP:" ++ show calcDate) i (constnt 0)
            comment _   = id

            -- getting current risk factors from oracle
            oracle = let ac = context <$> constraints ct in inquiryFs ev ("_" ++ show i) date "oracle" ac

            -- previous state
            st :: ContractStateMarlowe
            st =
              ContractStatePoly
                { nsc = useval "nsc" $ i P.- 1,
                  nt = useval "nt" $ i P.- 1,
                  isc = useval "isc" $ i P.- 1,
                  ipac = useval "ipac" $ i P.- 1,
                  feac = useval "feac" $ i P.- 1,
                  ipnr = useval "ipnr" $ i P.- 1,
                  ipcb = useval "ipcb" $ i P.- 1,
                  prnxt = useval "prnxt" $ i P.- 1,
                  tmd = useval "tmd" i,
                  prf = undefined,
                  sd = useval "sd" (timeToSlotNumber prevDate)
                }

            -- current risk factors
            rf :: RiskFactorsMarlowe
            rf =
              RiskFactorsPoly
                { o_rf_CURS = useval "o_rf_CURS" i,
                  o_rf_RRMO = useval "o_rf_RRMO" i,
                  o_rf_SCMO = useval "o_rf_SCMO" i,
                  pp_payoff = useval "pp_payoff" i
                }

            -- state transformation to current state
            stf = stateToContract <$> stateTransition ev rf prevDate calcDate st

            -- payoff
            pof =
              case payoffFs ev rf ct st prevDate calcDate of
                Nothing -> cont
                Just payoff ->
                  Let (payoffAt i) payoff $
                    -- TODO: should be done with Let constructor based on the actual
                    -- payoff that is derived from the observed risk factors.
                    --
                    -- But this would introduce exponential growth of the contract, since
                    -- the continuation is put into both branches of the If construct.
                    --
                    -- Using Cond allows to flip the sign of the payoff amount, but
                    -- not party and counterparty.
                    if amount cf > 0.0
                      then
                        invoice
                          "party"
                          "counterparty"
                          (UseValue $ payoffAt i)
                          date
                          cont
                      else
                        if amount cf < 0.0
                          then
                            invoice
                              "counterparty"
                              "party"
                              (NegValue $ UseValue $ payoffAt i)
                              date
                              cont
                          else cont
          in stf >>= \stf' -> return $ oracle . comment ev . stf' $ pof

      scheduleAcc :: Reader (CtxSTF Double LocalTime) Contract
      scheduleAcc =
        foldrM gen (postProcess Close) $
          L.zip5 projectedCashflows previousDates eventTypesOfCashflows paymentDayCashflows [1 ..]
   in runReader (stateInitialisation <$> initializeState <*> scheduleAcc) initCtx
  where
    fpSchedule, prSchedule, ipSchedule :: [LocalTime]
    fpSchedule = calculationDay <$> schedule FP ct
    prSchedule = calculationDay <$> schedule PR ct
    ipSchedule = calculationDay <$> schedule IP ct

    initCtx :: CtxSTF Double LocalTime
    initCtx = CtxSTF ct fpSchedule prSchedule ipSchedule (S.maturity ct)

    stateInitialisation :: ContractState -> Contract -> Contract
    stateInitialisation ContractStatePoly {..} =
      letval "tmd" 0 (marloweTime tmd)
        . letval "nt" 0 (constnt nt)
        . letval "ipnr" 0 (constnt ipnr)
        . letval "ipac" 0 (constnt ipac)
        . letval "feac" 0 (constnt feac)
        . letval "nsc" 0 (constnt nsc)
        . letval "isc" 0 (constnt isc)
        . letval "sd" 0 (marloweTime sd)
        . letval "prnxt" 0 (constnt prnxt)
        . letval "ipcb" 0 (constnt ipcb)

    postProcess :: Contract -> Contract
    postProcess cont =
      let ctr = constraints ct
          toAssert = genZeroRiskAssertions ct <$> (assertions =<< maybeToList ctr)
          compose = appEndo . mconcat . map Endo
       in compose toAssert cont

    inquiryFs :: EventType -> String -> Slot -> String -> Maybe AssertionContext -> Contract -> Contract
    inquiryFs ev timePosfix date oracle context continue =
      let oracleRole = Role $ TokenName $ fromString oracle

          letTemplate inputChoiceId inputOwner cont =
            Let
              (ValueId inputChoiceId)
              (ChoiceValue (ChoiceId inputChoiceId inputOwner))
              cont

          inputTemplate inputChoiceId inputOwner inputBound cont =
            When
              [ Case (Choice (ChoiceId inputChoiceId inputOwner) inputBound) $
                  letTemplate inputChoiceId inputOwner cont
              ]
              date
              Close

          inferBounds name ctx = case (name, ctx) of
            ("o_rf_RRMO", Just AssertionContext {..}) ->
              [Bound (toMarloweFixedPoint rrmoMin) (toMarloweFixedPoint rrmoMax)]
            _ -> [Bound 0 maxPseudoDecimalValue]

          riskFactorInquiry name =
            inputTemplate
              (fromString (name ++ timePosfix))
              oracleRole
              (inferBounds name context)

          riskFactorsInquiryEv AD = id
          riskFactorsInquiryEv SC = riskFactorInquiry "o_rf_SCMO"
          riskFactorsInquiryEv RR = riskFactorInquiry "o_rf_RRMO"
          riskFactorsInquiryEv PP = riskFactorInquiry "o_rf_CURS" . riskFactorInquiry "pp_payoff"
          riskFactorsInquiryEv _ =
            if enableSettlement ct
              then riskFactorInquiry "o_rf_CURS"
              else Let (ValueId (fromString ("o_rf_CURS" ++ timePosfix))) (constnt 1.0)
       in riskFactorsInquiryEv ev continue

    maxPseudoDecimalValue :: Integer
    maxPseudoDecimalValue = 100000000000000

    genZeroRiskAssertions :: ContractTerms -> Assertion -> Contract -> Contract
    genZeroRiskAssertions terms@ContractTermsPoly {ct_DCC = Just dcc, ..} NpvAssertionAgainstZeroRiskBond {..} continue =
      let cfs = genProjectedCashflows defaultRiskFactors terms

          dateToYearFraction :: LocalTime -> Double
          dateToYearFraction dt = _y dcc ct_SD dt ct_MD

          dateToDiscountFactor dt = (1 O.- zeroRiskInterest) ** dateToYearFraction dt

          accumulateAndDiscount :: Value Observation -> (CashFlow, Integer) -> Value Observation
          accumulateAndDiscount acc (cf, t) =
            let discountFactor = dateToDiscountFactor $ cashCalculationDay cf
                sign x = if amount cf < 0.0 then NegValue x else x
             in constnt discountFactor * (sign $ useval "payoff" t) + acc

          npv = foldl accumulateAndDiscount (constnt 0) (zip cfs [1 ..])
       in Assert (ValueLT (constnt expectedNpv) npv) continue
    genZeroRiskAssertions _ _ c = c
