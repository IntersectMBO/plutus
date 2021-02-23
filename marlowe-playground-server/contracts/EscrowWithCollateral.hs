{-# LANGUAGE OverloadedStrings #-}
module EscrowWithCollateral where

import           Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract


{- What does the vanilla contract look like?
  - if Alice and Bob choose
      - and agree: do it
      - and disagree: Carol decides
  - Carol also decides if timeout after one choice has been made;
  - refund if no choices are made.
-}

-- step1: bob's collateral
contract :: Contract
contract = When [Case (Deposit "bob" "bob" ada bobCollateral) contract2]
                10
                Close
-- step2: alice's collateral
contract2 :: Contract
contract2 = When [Case (Deposit "alice" "alice" ada aliceCollateral) contract3]
                20
                Close

-- step3: alice's payment
contract3 :: Contract
contract3 = When [Case (Deposit "alice" "alice" ada price) inner]
                30
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
    Pay "alice" (Party "blackhole") ada aliceCollateral (Pay "bob" (Party "blackhole") ada bobCollateral Close)

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
aliceChosen, bobChosen :: Value

aliceChosen = ChoiceValue (ChoiceId choiceName "alice")
bobChosen   = ChoiceValue (ChoiceId choiceName "bob")

defValue :: Value
defValue = Constant 42

-- Value under escrow
price :: Value
price = Constant 450

aliceCollateral :: Value
aliceCollateral = Constant 4500

bobCollateral :: Value
bobCollateral = Constant 4500

