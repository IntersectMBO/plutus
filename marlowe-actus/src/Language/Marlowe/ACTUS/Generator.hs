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
import           Data.Maybe                                                 (fromMaybe, isNothing, maybeToList)
import           Data.Monoid                                                (Endo (Endo, appEndo))
import           Data.String                                                (IsString (fromString))
import           Data.Time                                                  (Day)
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
import           Language.Marlowe.ACTUS.MarloweCompat                       (constnt, dayToSlotNumber,
                                                                             stateInitialisation, toMarloweFixedPoint,
                                                                             useval)
import           Language.Marlowe.ACTUS.Model.APPLICABILITY.Applicability   (validateTerms)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (initialize)
import           Language.Marlowe.ACTUS.Model.POF.PayoffFs                  (payoffFs)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionFs         (stateTransitionFs)
import           Language.Marlowe.ACTUS.Ops                                 as O (ActusNum (..), YearFractionOps (_y))
import           Ledger.Value                                               (TokenName (TokenName))
import           Prelude                                                    as P hiding (Fractional, Num, (*), (+), (/))

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
    let party        = Role $ TokenName $ fromString from
        counterparty = Role $ TokenName $ fromString to
    in  When
            [ Case
                    (Deposit party party ada amount)
                    (Pay party
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

maxPseudoDecimalValue :: Integer
maxPseudoDecimalValue = 100000000000000

inquiryFs
    :: EventType
    -> ContractTerms
    -> String
    -> Slot
    -> String
    -> Maybe AssertionContext
    -> Contract
    -> Contract
inquiryFs ev ct timePosfix date oracle context continue =
    let
        oracleRole = Role $ TokenName $ fromString oracle

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
            ("o_rf_RRMO", Just AssertionContext{..}) ->
                [Bound (toMarloweFixedPoint rrmoMin) (toMarloweFixedPoint rrmoMax)]
            _ -> [Bound 0 maxPseudoDecimalValue]

        riskFactorInquiry name = inputTemplate
            (fromString (name ++ timePosfix))
            oracleRole
            (inferBounds name context)

        riskFactorsInquiryEv AD = id
        riskFactorsInquiryEv SC = riskFactorInquiry "o_rf_SCMO"
        riskFactorsInquiryEv RR = riskFactorInquiry "o_rf_RRMO"
        riskFactorsInquiryEv PP = riskFactorInquiry "o_rf_CURS" .  riskFactorInquiry "pp_payoff"
        riskFactorsInquiryEv _ =
            if enableSettlement ct then riskFactorInquiry "o_rf_CURS"
            else Let (ValueId (fromString ("o_rf_CURS" ++ timePosfix))) (constnt 1.0)

    in
        riskFactorsInquiryEv ev continue

defaultRiskFactors :: EventType -> Day -> RiskFactors
defaultRiskFactors _ _ =
  RiskFactorsPoly
    { o_rf_CURS = 1.0,
      o_rf_RRMO = 1.0,
      o_rf_SCMO = 1.0,
      pp_payoff = 0.0
    }

genStaticContract :: ContractTerms -> Validation [TermValidationError] Contract
genStaticContract terms = genContract . setDefaultContractTermValues <$> validateTerms terms
    where
        genContract :: ContractTerms -> Contract
        genContract t =
            let
                cfs = genProjectedCashflows defaultRiskFactors t
                gen CashFlow {..}
                    | amount == 0.0 = id
                    | amount > 0.0
                    = invoice
                        "party"
                        "counterparty"
                        (Constant $ round amount)
                        -- Any collateral-related code is commented out, until implemented properly
                        -- (Constant 0)
                        (Slot $ dayToSlotNumber cashPaymentDay)
                    | otherwise
                    = invoice
                        "counterparty"
                        "party"
                        (Constant $ round $ - amount)
                        -- Any collateral-related code is commented out, until implemented properly
                        -- (Constant $ collateralAmount t)
                        (Slot $ dayToSlotNumber cashPaymentDay)
                -- Any collateral-related code is commented out, until implemented properly
                -- withCollateral cont =
                --     receiveCollateral
                --         "counterparty"
                --         (collateralAmount t)
                --         (dayToSlotNumber $ ct_SD t)
                --         cont
            -- Any collateral-related code is commented out, until implemented properly
            -- in Success . withCollateral $ foldr gen Close cfs
            in L.foldl' (flip gen) Close $ reverse cfs

genFsContract :: ContractTerms -> Validation [TermValidationError] Contract
genFsContract terms = genContract . setDefaultContractTermValues <$> validateTerms terms
    where
        genContract :: ContractTerms -> Contract
        genContract terms' =
            let
                postProcess cont =
                    let ctr = constraints terms'
                        toAssert = genZeroRiskAssertions terms' <$> (assertions =<< maybeToList ctr)
                        compose = appEndo . mconcat . map Endo
                    in compose toAssert cont

                payoffAt t = ValueId $ fromString $ "payoff_" ++ show t
                schedCfs = genProjectedCashflows defaultRiskFactors terms'
                schedEvents = cashEvent <$> schedCfs
                schedDates = Slot . dayToSlotNumber . cashPaymentDay <$> schedCfs
                previousDates = ct_SD terms' : (cashCalculationDay <$> schedCfs)
                cfsDirections = amount <$> schedCfs
                ctx = context <$> constraints terms'

                gen :: (CashFlow, Day, EventType, Slot, Double, Integer) -> Contract -> Contract
                gen (cf, prevDate, ev, date, r, t) cont =
                    inquiryFs ev terms' ("_" ++ show t) date "oracle" ctx
                    $ stateTransitionFs ev
                        RiskFactorsPoly {
                            o_rf_CURS = useval "o_rf_CURS" t
                          , o_rf_RRMO = useval "o_rf_RRMO" t
                          , o_rf_SCMO = useval "o_rf_SCMO" t
                          , pp_payoff = useval "pp_payoff" t
                        }
                        terms' t prevDate (cashCalculationDay cf)
                    $ Let (payoffAt t) (fromMaybe (constnt 0.0) pof)
                    $ if isNothing pof then cont
                    else if  r > 0.0   then
                        invoice
                            "party"
                            "counterparty"
                            (UseValue $ payoffAt t)
                            -- Any collateral-related code is commented out, until implemented properly
                            -- (Constant 0)
                            date
                            cont
                    else
                        invoice
                            "counterparty"
                            "party"
                            (NegValue $ UseValue $ payoffAt t)
                            -- Any collateral-related code is commented out, until implemented properly
                            -- (Constant $ collateralAmount terms)
                            date
                            cont
                    where pof = payoffFs ev
                                  RiskFactorsPoly {
                                      o_rf_CURS = useval "o_rf_CURS" t
                                    , o_rf_RRMO = useval "o_rf_RRMO" t
                                    , o_rf_SCMO = useval "o_rf_SCMO" t
                                    , pp_payoff = useval "pp_payoff" t
                                    }
                                  terms' (t P.- 1) prevDate (cashCalculationDay cf)
                scheduleAcc = foldr gen (postProcess Close) $
                    L.zip6 schedCfs previousDates schedEvents schedDates cfsDirections [1..]
                -- withCollateral cont = receiveCollateral "counterparty" (collateralAmount terms') (dayToSlotNumber $ ct_SD terms') cont
            -- in withCollateral $ initializeStateFs terms' scheduleAcc
            in initializeStateFs terms' scheduleAcc

        initializeStateFs :: ContractTerms -> Contract -> Contract
        initializeStateFs ct cont = maybe cont (flip stateInitialisation cont) (initialize ct)

genZeroRiskAssertions :: ContractTerms -> Assertion -> Contract -> Contract
genZeroRiskAssertions terms@ContractTerms{ct_DCC = Just dcc, ..} NpvAssertionAgainstZeroRiskBond{..} continue =
    let
        cfs = genProjectedCashflows defaultRiskFactors terms

        dateToYearFraction :: Day -> Double
        dateToYearFraction dt = _y dcc ct_SD dt ct_MD

        dateToDiscountFactor dt =  (1 O.- zeroRiskInterest) ** dateToYearFraction dt

        accumulateAndDiscount :: Value Observation -> (CashFlow, Integer) ->  Value Observation
        accumulateAndDiscount acc (cf, t) =
            let discountFactor = dateToDiscountFactor $ cashCalculationDay cf
                sign x = if amount cf < 0.0 then NegValue x else x
            in constnt discountFactor * (sign $ useval "payoff" t) + acc

        npv = foldl accumulateAndDiscount (constnt 0) (zip cfs [1..])
    in Assert (ValueLT (constnt expectedNpv) npv) continue
genZeroRiskAssertions _ _ c = c
