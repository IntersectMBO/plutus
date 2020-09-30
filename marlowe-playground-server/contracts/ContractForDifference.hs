{-# LANGUAGE OverloadedStrings #-}
module ContractForDifference where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

party :: Role 
party = Role "party"

partyAccount :: Account 
partyAccount = AccountId 0 party

counterParty :: Role
counterParty = Role "counterparty"

counterPartyAccount :: Account 
counterPartyAccount = AccountId 0 counterParty

partyCollateralToken :: Token
partyCollateralToken = (Token "" "")

partyCollateralAmount :: Constant
partyCollateralAmount = Constant 1000

counterPartyCollateralToken :: Token
counterPartyCollateralToken = (Token "" "")

counterPartyCollateralAmount :: Constant
counterPartyCollateralAmount = Constant 1000

endDate :: Integer
endDate = 1000

oracle :: Role
oracle = Role "oracle"

when :: Integer -> Action -> Contract -> Contract
when timeout action continue = When [Case action continue] 0 Close

before :: Integer -> Integer
before = id

partyCollateralDeposit :: Deposit
partyCollateralDeposit = 
    Deposit
        partyAccount
        party
        partyCollateralToken
        partyCollateralAmount

counterPartyCollateralDeposit :: Deposit
counterPartyCollateralDeposit = 
    Deposit
        partyAccount
        party
        partyCollateralToken
        partyCollateralAmount
            
receive :: String -> Contract -> Contract
receive value continue = (Choice (ChoiceId value oracle) [Bound 0 100000])

read :: String -> (Value Observation)
read value = ChoiceValue (ChoiceId "price1" oracle))

waitFor :: Integer -> Contract -> Contract
waitFor delay continue =  When [] delay continue

then' :: Contract -> Contract
then' = id

else' :: Contract -> Contract
else' = id

contract :: Contract
contract = 
    let 
        max val1 val2 = Cond (ValueGE val1 val2) val2 val1
    in 
        when (before 100) partyCollateralDeposit $
        when (before 100) counterPartyCollateralDeposit $
        when (before 100) (receive "price1") $ 
        waitFor endDate $
        when (before $ endDate + 100) (receive "price2") $
        Let "diff" (SubValue (read "price1") (read "price2")) $
        If (ValueLT (UseValue "diff") (Constant 0)) 
            (then' 
                Let "absdiff" (NegValue (UseValue "diff")) $
                (let payoff = max (UseValue "absdiff") counterPartyCollateralDeposit
                in Pay partyAccount counterParty counterPartyCollateralToken payoff) $
                Close
            )
            (else' 
                (let payoff = max (UseValue "diff") partyCollateralDeposit
                in Pay partyAccount counterParty counterPartyCollateralToken payoff) $
                Close
            )