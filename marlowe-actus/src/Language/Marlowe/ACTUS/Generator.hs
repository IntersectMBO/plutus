{-# LANGUAGE RecordWildCards #-}

{-| = ACTUS Generator

This module contains templates for Marlowe constructs required by ACTUS logic

-}

module Language.Marlowe.ACTUS.Generator
    ( genStaticContract
    , genFsContract
    )
where

import qualified Data.List                                                  as L (foldl', zip6)
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
                                                                             RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (Assertion (..), AssertionContext (..),
                                                                             Assertions (..), ContractTerms (..),
                                                                             TermValidationError (..),
                                                                             setDefaultContractTermValues)
import           Language.Marlowe.ACTUS.Definitions.Schedule                (CashFlow (..))
import           Language.Marlowe.ACTUS.MarloweCompat                       (constnt, stateInitialisation,
                                                                             timeToSlotNumber, toMarloweFixedPoint,
                                                                             useval)
import           Language.Marlowe.ACTUS.Model.APPLICABILITY.Applicability   (validateTerms)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (initialize)
import           Language.Marlowe.ACTUS.Model.POF.PayoffFs                  (payoffFs)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionFs         (stateTransitionFs)

import           Language.Marlowe.ACTUS.Ops                                 as O (ActusNum (..), YearFractionOps (_y))
import           Ledger.Value                                               (TokenName (TokenName))
import           Prelude                                                    as P hiding (Fractional, Num, (*), (+), (/))


{-| Static contracts - risk factors are known in advance
-}

-- |genStaticContract generates a Marlowe contracts from the validated contract terms applying
-- the default risk factors
genStaticContract :: ContractTerms -> Validation [TermValidationError] Contract
genStaticContract = fmap genStaticContract' . validateTerms . setDefaultContractTermValues

-- |genStaticContract' generates a Marlowe contracts from the given contract terms applying
-- the default risk factors
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
            -- Any collateral-related code is commented out, until implemented properly
            -- (Constant 0)
            (Slot $ timeToSlotNumber cashPaymentDay)
        | otherwise =
          invoice
            "counterparty"
            "party"
            (Constant $ round $ - amount)
            -- Any collateral-related code is commented out, until implemented properly
            -- (Constant $ collateralAmount ct)
            (Slot $ timeToSlotNumber cashPaymentDay)
   in -- Any collateral-related code is commented out, until implemented properly
      -- withCollateral cont =
      --     receiveCollateral
      --         "counterparty"
      --         (collateralAmount ct)
      --         (timeToSlotNumber $ ct_SD ct)
      --         cont
      -- Any collateral-related code is commented out, until implemented properly
      -- in Success . withCollateral $ foldr gen Close cfs
      L.foldl' (flip gen) Close $ reverse cfs


-- receiveCollateral :: String -> Integer -> Integer -> Contract -> Contract
-- Any collateral-related code is commented out, until implemented properly
-- receiveCollateral from amount timeout continue =
--    if amount == 0
--        then continue
--        else
--            let party = Role $ TokenName $ fromString from
--            in  When
--                    [ Case
--                        (Deposit party party ada (Constant amount))
--                            continue
--                    ]
--                    (Slot timeout)
--                    Close

-- Any collateral-related code is commented out, until implemented properly
-- invoice :: String -> String -> Value Observation -> Value Observation -> Slot -> Contract -> Contract
-- invoice from to amount collateralAmount timeout continue =
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
-- Any collateral-related code is commented out, until implemented properly
-- (Pay party
--     (Party counterparty)
--     ada
--     collateralAmount
--     Close
-- )

defaultRiskFactors :: EventType -> LocalTime -> RiskFactors
defaultRiskFactors _ _ =
  RiskFactorsPoly
    { o_rf_CURS = 1.0,
      o_rf_RRMO = 1.0,
      o_rf_SCMO = 1.0,
      pp_payoff = 0.0
    }

{-| Dynamic contracts - risk factors are observed at a given point in time
#-}

genFsContract :: ContractTerms -> Validation [TermValidationError] Contract
genFsContract = fmap genFsContract' . validateTerms . setDefaultContractTermValues

genFsContract' :: ContractTerms -> Contract
genFsContract' ct =
  let payoffAt t = ValueId $ fromString $ "payoff_" ++ show t
      schedCfs = genProjectedCashflows defaultRiskFactors ct
      schedEvents = cashEvent <$> schedCfs
      schedDates = Slot . timeToSlotNumber . cashPaymentDay <$> schedCfs
      previousDates = ct_SD ct : (cashCalculationDay <$> schedCfs)
      cfsDirections = amount <$> schedCfs
      ctx = context <$> constraints ct

      gen :: (CashFlow, LocalTime, EventType, Slot, Double, Integer) -> Contract -> Contract
      gen (cf, prevDate, ev, date, r, t) cont =
          observe
        $ stateTransitionFunction
        $ case payoffFunction of
            Nothing -> cont
            Just payoff ->
              Let (payoffAt t) payoff $
                -- TODO: should be done with Let constructor based on the actual
                -- payoff that is derived from the observed risk factors.
                --
                -- But this would introduce exponential growth of the contract, since
                -- the continuation is put into both branches of the If construct.
                --
                -- Using Cond allows to flip the sign of the payoff amount, but
                -- not party and counterparty.
                if r > 0.0
                  then
                    invoice
                      "party"
                      "counterparty"
                      (UseValue $ payoffAt t)
                      -- Any collateral-related code is commented out, until implemented properly
                      -- (Constant 0)
                      date
                      cont
                  else
                    if r < 0.0
                      then
                        invoice
                          "counterparty"
                          "party"
                          (NegValue $ UseValue $ payoffAt t)
                          -- Any collateral-related code is commented out, until implemented properly
                          -- (Constant $ collateralAmount terms)
                          date
                          cont
                      else cont
        where
          cd = cashCalculationDay cf
          rf = riskFactors t
          observe = inquiryFs ev ("_" ++ show t) date "oracle" ctx
          stateTransitionFunction = stateTransitionFs ev rf ct t prevDate cd
          payoffFunction = payoffFs ev rf ct (t P.- 1) prevDate cd

      scheduleAcc =
        foldr gen (postProcess Close) $
          L.zip6 schedCfs previousDates schedEvents schedDates cfsDirections [1 ..]
   in -- withCollateral cont = receiveCollateral "counterparty" (collateralAmount ct) (timeToSlotNumber $ ct_SD ct) cont
      -- in withCollateral $ initializeStateFs scheduleAcc
      initializeStateFs scheduleAcc

  where

    postProcess cont =
      let ctr = constraints ct
          toAssert = genZeroRiskAssertions ct <$> (assertions =<< maybeToList ctr)
          compose = appEndo . mconcat . map Endo
       in compose toAssert cont

    initializeStateFs :: Contract -> Contract
    initializeStateFs cont = maybe cont (flip stateInitialisation cont) (initialize ct)

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

    riskFactors :: Integer -> RiskFactorsPoly (Value Observation)
    riskFactors t =
      RiskFactorsPoly
        { o_rf_CURS = useval "o_rf_CURS" t,
          o_rf_RRMO = useval "o_rf_RRMO" t,
          o_rf_SCMO = useval "o_rf_SCMO" t,
          pp_payoff = useval "pp_payoff" t
        }

    genZeroRiskAssertions :: ContractTerms -> Assertion -> Contract -> Contract
    genZeroRiskAssertions terms@ContractTerms {ct_DCC = Just dcc, ..} NpvAssertionAgainstZeroRiskBond {..} continue =
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
