module Component.Transfer.Types where

import Prologue
import Data.BigInteger (BigInteger)
import Marlowe.Semantics (AccountId, Party, Token)

-- Here's my justification for why this module should exist:
-- In the semantics, there are two types that are used to represent the
-- transfer of assets. The IDeposit Action is used to represent the transfer of
-- assets from a wallet to an account. The Payment type is used to represent
-- the transfer of assets from an account to either an account or a wallet,
-- depending on the constructor used to create the Payee (Party = Wallet,
-- Account = Account)
--
-- But this is a view model, and we want to reuse the component used to render
-- this information. So we use one type to represent all three of these cases.
--
-- Note that all the types are basically the same. The additional data
-- constructors are purely to make the model more self-documenting
type Transfer
  = { sender :: Participant
    , recipient :: Participant
    , token :: Token
    , quantity :: BigInteger
    , termini :: Termini
    }

data Termini
  = AccountToAccount AccountId AccountId
  | AccountToWallet AccountId Party
  | WalletToAccount Party AccountId

type Participant
  = { nickname :: Maybe String
    , isCurrentUser :: Boolean
    }

type Nickname
  = String
