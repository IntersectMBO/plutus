{-# LANGUAGE RecordWildCards #-}

{- This module contains templates for Marlowe constructs required by ACTUS logic -}
module Language.Marlowe.ACTUS.Generator
    (
    genStaticContract
    , genFsContract
    )
where

import qualified Data.List                                                as L (zip6)
import           Data.Maybe                                               (fromMaybe, isNothing, maybeToList)
import           Data.Monoid
import           Data.String                                              (IsString (fromString))
import           Data.Time                                                (Day)
import           Data.Validation                                          (Validation (..))
import           Language.Marlowe                                         (Action (Choice, Deposit), Bound (Bound),
                                                                           Case (Case), ChoiceId (ChoiceId),
                                                                           Contract (Close, Let, Pay, When),
                                                                           Observation, Party (Role), Payee (Party),
                                                                           Slot (..),
                                                                           Value (ChoiceValue, Constant, NegValue, UseValue),
                                                                           ValueId (ValueId), ada)
import           Language.Marlowe.ACTUS.Analysis                          (genProjectedCashflows, genZeroRiskAssertions)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents        (EventType (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms         (AssertionContext (..), Assertions (..),
                                                                           ContractTerms (constraints, ct_CURS, ct_SD, collateralAmount),
                                                                           TermValidationError (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule              (CashFlow (..))
import           Language.Marlowe.ACTUS.MarloweCompat                     (constnt, dayToSlotNumber,
                                                                           toMarloweFixedPoint)
import           Language.Marlowe.ACTUS.Model.APPLICABILITY.Applicability (validateTerms)
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationFs  (inititializeStateFs)
import           Language.Marlowe.ACTUS.Model.POF.PayoffFs                (payoffFs)
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionFs       (stateTransitionFs)
import           Ledger.Value                                             (TokenName (TokenName))


receiveCollateral :: String -> Integer -> Integer -> Contract -> Contract
receiveCollateral from amount timeout continue =
    if amount == 0 
        then continue
        else
            let party        = Role $ TokenName $ fromString from
            in  When
                    [ Case
                        (Deposit party party ada (Constant amount))
                            continue
                    ]
                    (Slot timeout)
                    Close  


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
        riskFactorsInquiryEv PP =
            riskFactorInquiry "o_rf_CURS" .
                riskFactorInquiry "pp_payoff"
        riskFactorsInquiryEv _ =
            if ct_CURS ct then riskFactorInquiry "o_rf_CURS"
            else Let (ValueId (fromString ("o_rf_CURS" ++ timePosfix))) (constnt 1.0)
    in
        riskFactorsInquiryEv ev continue


{- Note [ContractTerms and Maybe]
Throughout the contract generation, ContractTerms fields are commonly accessed
with what appears to be an unchecked `fromJust`. There's not much backing up
the assertion that one of those won't fail other than the applicability model
right now. The applicability model (validateTerms) enforces that certain fields
(e.g ContractType, Notional, etc.) are required, and contract generation will
fail if they aren't provided.

The plans for better type safety were also outlined in this comment:
https://github.com/input-output-hk/plutus/pull/2440#issuecomment-722329158
-}

genStaticContract :: ContractTerms -> Validation [TermValidationError] Contract
genStaticContract terms =
    case validateTerms terms of
        Failure errs -> Failure errs
        Success t ->
            let
                cfs = genProjectedCashflows t
                gen CashFlow {..}
                    | amount == 0.0 = id
                    | amount > 0.0
                    = invoice "party" "counterparty" (Constant $ round amount) (Slot $ dayToSlotNumber cashPaymentDay)
                    | otherwise
                    = invoice "counterparty" "party" (Constant $ round $ - amount) (Slot $ dayToSlotNumber cashPaymentDay)
                withCollateral cont = receiveCollateral "party" (collateralAmount t) (dayToSlotNumber $ ct_SD t) cont
            in Success $ withCollateral $ foldl (flip gen) Close cfs


genFsContract :: ContractTerms -> Validation [TermValidationError] Contract
genFsContract terms =
    case validateTerms terms of
        Failure errs -> Failure errs
        Success _ ->
            let
                postProcess cont =
                    let ctr = constraints terms
                        toAssert = genZeroRiskAssertions terms <$> (assertions =<< maybeToList ctr)
                        compose = appEndo . mconcat . map Endo
                    in compose toAssert cont

                payoffAt t = ValueId $ fromString $ "payoff_" ++ show t
                schedCfs = genProjectedCashflows terms
                schedEvents = cashEvent <$> schedCfs
                schedDates = Slot . dayToSlotNumber . cashPaymentDay <$> schedCfs
                previousDates = ct_SD terms : (cashCalculationDay <$> schedCfs)
                cfsDirections = amount <$> schedCfs
                ctx = context <$> constraints terms

                gen :: (CashFlow, Day, EventType, Slot, Double, Integer) -> Contract -> Contract
                gen (cf, prevDate, ev, date, r, t) cont =
                    inquiryFs ev terms ("_" ++ show t) date "oracle" ctx
                    $ stateTransitionFs ev terms t prevDate (cashCalculationDay cf)
                    $ Let (payoffAt t) (fromMaybe (constnt 0.0) pof)
                    $ if isNothing pof then cont
                    else if  r > 0.0   then invoice "party" "counterparty" (UseValue $ payoffAt t) date cont
                    else                    invoice "counterparty" "party" (NegValue $ UseValue $ payoffAt t) date cont
                    where pof = payoffFs ev terms t (t - 1) prevDate (cashCalculationDay cf)
                scheduleAcc = foldr gen (postProcess Close) $
                    L.zip6 schedCfs previousDates schedEvents schedDates cfsDirections [1..]
                withCollateral cont = receiveCollateral "party" (collateralAmount terms) (dayToSlotNumber $ ct_SD terms) cont
            in Success $ withCollateral $ inititializeStateFs terms scheduleAcc
