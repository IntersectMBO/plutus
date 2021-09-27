module Component.Transfer.Types where

import Prologue
import Data.BigInteger (BigInteger)
import Marlowe.Semantics (AccountId, Party)

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
data Transfer
  = AccountToAccount Account Account BigInteger
  | AccountToWallet Account Wallet BigInteger
  | WalletToAccount Wallet Account BigInteger

data Owner
  = CurrentUser String
  | OtherUser (Maybe String)

data Account
  = Account AccountId Owner

data Wallet
  = Wallet Party Owner
