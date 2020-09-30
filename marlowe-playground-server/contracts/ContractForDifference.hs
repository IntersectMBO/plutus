{-# LANGUAGE OverloadedStrings #-}
module ContractForDifference where

import           Language.Marlowe
import           Data.String                                       (IsString (fromString))

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

partyCollateralToken :: Token
partyCollateralToken = (Token "" "")

partyCollateralAmount :: (Value Observation)
partyCollateralAmount = Constant 1000

counterPartyCollateralToken :: Token
counterPartyCollateralToken = (Token "" "")

counterPartyCollateralAmount :: (Value Observation)
counterPartyCollateralAmount = Constant 1000

endDate :: Integer
endDate = 1000

oracle :: Party
oracle = Role "oracle"

when :: Integer -> Action -> Contract -> Contract
when timeout action continue = When [Case action continue] (Slot timeout) Close

before :: Integer -> Integer
before = id

partyCollateralDeposit :: Action
partyCollateralDeposit = 
    Deposit
        partyAccount
        party
        partyCollateralToken
        partyCollateralAmount

counterPartyCollateralDeposit :: Action
counterPartyCollateralDeposit = 
    Deposit
        partyAccount
        party
        partyCollateralToken
        partyCollateralAmount
            
receiveValue :: String -> Action
receiveValue value = (Choice (ChoiceId (fromString value) oracle) [Bound 0 100000])

readValue :: String -> (Value Observation)
readValue value = ChoiceValue (ChoiceId (fromString value) oracle)

waitFor :: Integer -> Contract -> Contract
waitFor delay continue =  When [] (Slot delay) continue

then' :: Contract -> Contract
then' = id

else' :: Contract -> Contract
else' = id

letValue :: String -> (Value Observation) -> Contract -> Contract
letValue value = Let (ValueId $ fromString value)

contract :: Contract
contract = 
    let 
        maximum val1 val2 = Cond (ValueGE val1 val2) val2 val1
    in 
        when (before 100) partyCollateralDeposit $
        when (before 100) counterPartyCollateralDeposit $
        when (before 100) (receiveValue "price1") $ 
        waitFor endDate $
        when (before $ endDate + 100) (receiveValue "price2") $
        letValue "diff" (SubValue (readValue "price1") (readValue "price2")) $
        If (ValueLT (UseValue "diff") (Constant 0)) 
            (then' $ 
                letValue "absdiff" (NegValue (UseValue "diff")) $
                (let payoff = maximum (UseValue "absdiff") counterPartyCollateralAmount
                in Pay partyAccount (Party counterParty) counterPartyCollateralToken payoff) $
                Close
            )
            (else' $
                (let payoff = maximum (UseValue "diff") partyCollateralAmount
                in Pay partyAccount (Party counterParty) counterPartyCollateralToken payoff) $
                Close
            )