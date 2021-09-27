module Component.ConfirmInput.Types where

import Contract.Types as Contract
import Data.BigInteger (BigInteger)
import Marlowe.Execution.Types (NamedAction)
import Marlowe.Semantics (Slot) as Semantics

type Input
  = { action :: NamedAction
    , contractState :: Contract.StartedState
    , currentSlot :: Semantics.Slot
    , transactionFeeQuote :: BigInteger
    , userNickname :: String
    , walletBalance :: BigInteger
    }
