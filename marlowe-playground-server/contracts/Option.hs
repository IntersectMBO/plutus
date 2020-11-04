{-# LANGUAGE OverloadedStrings #-}
module Option where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

contract :: Contract
contract = When
    []
    10
    (When
        [Case
            (Choice
                (ChoiceId
                    "exercise"
                    (Role "buyer")
                )
                [Bound 0 1]
            )
            (Let
                "payoff"
                (Cond
                    (ValueEQ
                        (ChoiceValue
                            (ChoiceId "exercise" (Role "buyer"))
                        )
                        (Constant 1)
                    )
                    (Constant 1)
                    (Constant 0)
                )
                (When
                    [Case
                        (Deposit
                            (Role "seller")
                            (Role "seller")
                            (Token "" "")
                            (UseValue "payoff")
                        )
                        (Pay
                            (Role "seller")
                            (Party (Role "buyer"))
                            (Token "" "")
                            (UseValue "payoff")
                            Close
                        )]
                    120 Close
                )
            )]
        110 Close
    )

