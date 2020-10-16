{-# LANGUAGE OverloadedStrings #-}
module Option where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

contract :: Contract
contract = When
    [Case
        (Deposit
            (Role "party")
            (Role "party")
            (Token "" "")
            (Constant 1000)
        )
        (When
            [Case
                (Deposit
                    (Role "counterparty")
                    (Role "counterparty")
                    (Token "tethered" "bitcoin")
                    (Constant 1)
                )
                (When
                    [Case
                        (Choice
                            (ChoiceId
                                "exercise"
                                (Role "party")
                            )
                            [Bound 0 1]
                        )
                        (If
                            (ValueEQ
                                (ChoiceValue
                                    (ChoiceId
                                        "exercise"
                                        (Role "party")
                                    ))
                                (Constant 1)
                            )
                            (Pay
                                (Role "counterparty")
                                (Party (Role "party"))
                                (Token "tethered" "bitcoin")
                                (Constant 1)
                                (Pay
                                    (Role "party")
                                    (Party (Role "counterparty"))
                                    (Token "" "")
                                    (Constant 1000)
                                    Close
                                )
                            )
                            (Pay
                                (Role "party")
                                (Party (Role "counterparty"))
                                (Token "" "")
                                (Constant 100)
                                Close
                            )
                        )]
                    1000 Close
                )]
            10 Close
        )]
    10 Close
