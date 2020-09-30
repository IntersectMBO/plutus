{-# LANGUAGE OverloadedStrings #-}
module ContractForDifference where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract

contract :: Contract
contract = When
    [Case
        (Deposit
            (AccountId
                0
                (Role "party")
            )
            (Role "party")
            (Token "" "")
            (Constant 1000)
        )
        (When
            [Case
                (Deposit
                    (AccountId
                        0
                        (Role "counterparty")
                    )
                    (Role "counterparty")
                    (Token "" "")
                    (Constant 1000)
                )
                (When
                    [Case
                        (Choice
                            (ChoiceId
                                "price1"
                                (Role "oracle")
                            )
                            [Bound 0 100000]
                        )
                        (When
                            []
                            10000
                            (When
                                [Case
                                    (Choice
                                        (ChoiceId 
                                            "price2" 
                                            (Role "oracle"))
                                        [Bound 0 100000]
                                    )
                                    (Let
                                        "diff"
                                        (SubValue
                                            (ChoiceValue
                                                (ChoiceId
                                                    "price1"
                                                    (Role "oracle")
                                                ))
                                            (ChoiceValue
                                                (ChoiceId
                                                    "price2"
                                                    (Role "oracle")
                                                ))
                                        )
                                        (If
                                            (ValueLT
                                                (UseValue "diff")
                                                (Constant 0)
                                            )
                                            (Let
                                                "absdiff"
                                                (NegValue (UseValue "diff"))
                                                (Pay
                                                    (AccountId
                                                        1
                                                        (Role "party")
                                                    )
                                                    (Party (Role "counterparty"))
                                                    (Token "" "")
                                                    (Cond
                                                        (ValueGE
                                                            (UseValue "absdiff")
                                                            (Constant 1000)
                                                        )
                                                        (Constant 1000)
                                                        (UseValue "absdiff")
                                                    )
                                                    Close 
                                                )
                                            )
                                            (Pay
                                                (AccountId
                                                    1
                                                    (Role "counterparty")
                                                )
                                                (Party (Role "party"))
                                                (Token "" "")
                                                (Cond
                                                    (ValueGE
                                                        (UseValue "diff")
                                                        (Constant 1000)
                                                    )
                                                    (Constant 1000)
                                                    (UseValue "diff")
                                                )
                                                Close 
                                            )
                                        )
                                    )]
                                10000 Close 
                            )
                        )]
                    0 Close 
                )]
            0 Close 
        )]
    0 Close 

