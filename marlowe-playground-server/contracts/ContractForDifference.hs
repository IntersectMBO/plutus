{-# LANGUAGE OverloadedStrings #-}
module ContractForDifference where

import           Data.String      (IsString (fromString))
import           Language.Marlowe
import           Prelude          hiding (Fractional, Num, (*), (-), (/), (<))

main :: IO ()
main = print . pretty $ contract

party :: Party
party = Role "party"

partyAccount :: AccountId
partyAccount = AccountId 0 party

counterParty :: Party
counterParty = Role "counterparty"

counterPartyAccount :: AccountId
counterPartyAccount = AccountId 0 counterParty

oracle :: Party
oracle = Role "oracle"

waitForEvent :: Action -> Integer -> Contract -> Contract -> Contract
waitForEvent action timeout alternative continue = When [Case action continue] (Slot timeout) alternative

before :: Integer -> Integer
before = id

orElse :: Contract -> Contract
orElse = id

receiveValue :: String -> Action
receiveValue val = (Choice (ChoiceId (fromString val) oracle) [Bound 0 100000])

readValue :: String -> (Value Observation)
readValue val = ChoiceValue (ChoiceId (fromString val) oracle)

waitFor :: Integer -> Contract -> Contract
waitFor delay continue =  When [] (Slot delay) continue

checkIf :: Observation -> Contract -> Contract -> Contract
checkIf = If

thenDo :: Contract -> Contract
thenDo = id

elseDo :: Contract -> Contract
elseDo = id

letValue :: String -> (Value Observation) -> Contract -> Contract
letValue val = Let (ValueId $ fromString val)

useValue :: String -> (Value Observation)
useValue = UseValue . fromString

value :: Integer -> (Value Observation)
value = Constant

(-) :: (Value Observation) -> (Value Observation) -> (Value Observation)
(-) = SubValue

(<) :: (Value Observation) -> (Value Observation) -> Observation
(<) = ValueLT

from :: AccountId -> AccountId
from = id

to :: Party -> Payee
to = Party

with :: Token -> Token
with = id

end :: Contract
end = Close

amountOf :: (Value Observation) -> (Value Observation)
amountOf = id

contract :: Contract
contract =
    let

        partyCollateralToken = (Token "" "")
        partyCollateralAmount = value 1000
        counterPartyCollateralToken = (Token "" "")
        counterPartyCollateralAmount = value 1000
        endDate = 1000

        partyCollateralDeposit =
            Deposit
                partyAccount
                party
                partyCollateralToken
                partyCollateralAmount

        counterPartyCollateralDeposit =
            Deposit
                counterPartyAccount
                counterParty
                counterPartyCollateralToken
                counterPartyCollateralAmount

        maxValue val1 val2 = Cond (ValueGE val1 val2) val2 val1
    in
        waitForEvent partyCollateralDeposit (before 100) (orElse end) $
        waitForEvent counterPartyCollateralDeposit (before 100) (orElse end) $
        waitForEvent (receiveValue "price1") (before 100) (orElse end) $
        waitFor endDate $
        waitForEvent (receiveValue "price2") (before $ endDate + 100) (orElse end) $
        letValue "delta" (readValue "price1" - readValue "price2") $
        checkIf (useValue "delta" < value 0)
            (thenDo $
                letValue "absdelta" (value 0 - useValue "delta") $
                (let payoff = maxValue (useValue "absdelta") counterPartyCollateralAmount
                in Pay
                    (from partyAccount)
                    (to counterParty)
                    (with partyCollateralToken)
                    (amountOf payoff)) $
                end
            )
            (elseDo $
                (let payoff = maxValue (useValue "delta") partyCollateralAmount
                in Pay
                    (from counterPartyAccount)
                    (to party)
                    (with counterpPartyCollateralToken)
                    (amountOf payoff)) $
                end
            )
