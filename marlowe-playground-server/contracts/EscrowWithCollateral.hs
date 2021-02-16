{-# LANGUAGE OverloadedStrings #-}
module EscrowWithCollateral where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract


{- What does the vanilla contract look like?
  - if Alice and Bob choose
      - and agree: do it
      - and disagree: Carol decides
  - Carol also decides if timeout after one choice has been made;
  - refund if no choices are made.
-}

contract :: Contract
contract = When [Case (Deposit "bob" "bob" ada bobCollateral) contract]
                10
                Close

collateralAlice :: Contract
collateralAlice = When [Case (Deposit "alice" "alice" ada aliceCollateral) escrow]
                10
                Close

escrow :: Contract
escrow = When [Case (Deposit "alice" "alice" ada price) inner]
                10
                Close

inner :: Contract
inner =
  When [ Case aliceChoice
              (When [ Case bobChoice
                          (If (aliceChosen `ValueEQ` bobChosen)
                             agreement
                             destroyCollateral) ]
                    60
                    destroyCollateral)
        ]
        40
        destroyCollateral

-- The contract to follow when Alice and Bob have made the same choice.
agreement :: Contract
agreement =
  If
    (aliceChosen `ValueEQ` Constant 0)
    (Pay "alice" (Party "bob") ada price Close)
    Close

-- The contract to follow when Alice and Bob disagree
destroyCollateral :: Contract
destroyCollateral =
    (Pay "alice" (Party "blackhole") ada aliceCollateral (Pay "bob" (Party "blackhole") ada bobCollateral Close))

-- Names for choices
pay,refund,both :: [Bound]

pay    = [Bound 0 0]
refund = [Bound 1 1]
both   = [Bound 0 1]

choiceName :: ChoiceName
choiceName = "choice"

choice :: Party -> [Bound] -> Action
choice party = Choice (ChoiceId choiceName party)

-- Name choices according to person making choice and choice made

alicePay, aliceRefund, aliceChoice, bobPay, bobRefund, bobChoice, carolPay, carolRefund, carolChoice :: Action

alicePay    = choice "alice" pay
aliceRefund = choice "alice" refund
aliceChoice = choice "alice" both

bobPay    = choice "bob" pay
bobRefund = choice "bob" refund
bobChoice = choice "bob" both

carolPay    = choice "carol" pay
carolRefund = choice "carol" refund
carolChoice = choice "carol" both

-- the values chosen in choices
aliceChosen, bobChosen :: (Value Observation)

aliceChosen = ChoiceValue (ChoiceId choiceName "alice")
bobChosen   = ChoiceValue (ChoiceId choiceName "bob")

defValue :: (Value Observation)
defValue = Constant 42

-- Value under escrow
price :: (Value Observation)
price = Constant 450

aliceCollateral :: (Value Observation)
aliceCollateral = Constant 4500

bobCollateral :: (Value Observation)
bobCollateral = Constant 4500

