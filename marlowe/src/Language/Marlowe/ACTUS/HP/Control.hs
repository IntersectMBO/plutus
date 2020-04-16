{- This module contains templates for Marlowe constructs required by ACTUS logic -}

module Language.Marlowe.ACTUS.HP.Control where

import Language.Marlowe
import Data.Time
import Data.Time.Clock
import Data.Time.Clock.POSIX
import Data.Time.Clock.System
import Wallet 
import Ledger.Crypto
import Ledger.Value
import Data.String (IsString (fromString))
import Language.PlutusTx.AssocMap (Map)
import qualified Language.PlutusTx.AssocMap as Map
import Data.Maybe
import qualified Data.Maybe as Maybe

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

depositAndPay :: AccountIdentifier -> From -> To -> Day -> Amount -> Currency -> Tkn -> Continuation -> Contract
depositAndPay accId from to date amount currency token continue = 
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


-- todo: read ContractId, read eventType, read riskFactors, read proposed payoff amount, 
-- t0 t1 t2 - just counter
readProposedEvent :: Case Contract
readProposedEvent = let
    choiceOwner = Role $ TokenName $ fromString "oracle"
    choiceDefault = (Constant 0)
    choiceValueBound = [Bound 0 1000000]
    choiceEventTypeBound = [Bound 1 1]
    in
    Case
        (Choice
            (ChoiceId
                (fromString "eventType_t0")
                choiceOwner
            )
            choiceEventTypeBound
        )
        (When
            [Case
                (Choice
                    (ChoiceId
                        (fromString "riskFactor1_t0")
                        choiceOwner
                    )
                    choiceValueBound
                )
                (Let
                    (fromString "eventType_t0")
                    (ChoiceValue
                        (ChoiceId
                            (fromString "eventType_t0")
                            choiceOwner
                        )
                        choiceDefault
                    )
                    (Let
                        (fromString "riskFactor1_t0")
                        (ChoiceValue
                            (ChoiceId
                                (fromString "eventType_t0")
                                choiceOwner
                            )
                            choiceDefault
                        )
                        Close 
                    )
                )]
            0 Close 
        )

