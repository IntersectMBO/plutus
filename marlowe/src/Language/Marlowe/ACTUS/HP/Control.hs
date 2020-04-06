module Language.Marlowe.ACTUS.HP.Control where

import Language.Marlowe
import Data.Time
import Data.Time.Clock
import Data.Time.Clock.POSIX
import Data.Time.Clock.System

type Currency = String
type Tkn = String
type Amount = Integer
type From = Party
type To = Party
type AccountIdentifier = Int
type Continuation = Contract

cardanoEpochStart = 100

dayToSlotNumber :: Day -> Integer
dayToSlotNumber d = let
    (MkSystemTime secs _) = utcToSystemTime (UTCTime d 0)
    in fromIntegral secs - cardanoEpochStart `mod` 20

depositAndPay :: Day -> AccountIdentifier -> From -> To -> Amount -> Currency -> Tkn -> Continuation -> Contract
depositAndPay date accId from to amount currency token continue = 
    let token = ada --todo (Token currency token)
    in 
    When
    [Case
        (Deposit
            (AccountId
                0
                to
            )
            from
            token
            (Constant amount)
        )
        (If
            (ValueLE
                SlotIntervalStart 
                (Constant (dayToSlotNumber date))
            )
            (Pay
                (AccountId
                    1
                    from -- (Role from)
                )
                (Party to) --(Role to))
                token
                (Constant amount)
                continue 
            )
            Close 
        )]
    100 Close 

-- todo unscheduled events handler

-- todo Plutus event loop
    