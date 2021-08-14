module Marlowe.PAB
  ( transactionFee
  , contractCreationFee
  , PlutusAppId(..)
  , MarloweParams(..)
  , ValidatorHash
  , MarloweData(..)
  , ContractHistory(..)
  ) where

import Prelude
import Data.BigInteger (BigInteger, fromInt)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple)
import Data.UUID (UUID)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Contract, State, TransactionInput)
import Plutus.V1.Ledger.Value (CurrencySymbol)

-- In the Marlowe PAB, transactions have a fixed cost of 10 lovelace; in the real node, transaction
-- fees will vary, but this will serve as an approximation for now.
transactionFee :: BigInteger
transactionFee = fromInt 10

-- FIXME: it appears that creating a contract currently requires three transactions, but I believe it
-- should be possible with one; check this with Alex
contractCreationFee :: BigInteger
contractCreationFee = transactionFee * (fromInt 3)

{-
A `PlutusAppId` is used to identify an instance of a Plutus "contract" in the PAB. In the PAB code it is
called `ContractInstanceId` - as above, we don't refer to "contracts" here so as to avoid confusion with
*Marlowe* contracts. This is converted to a `ContractInstanceId` that the PAB understands by the `Bridge`
module.
-}
newtype PlutusAppId
  = PlutusAppId UUID

derive instance newtypePlutusAppId :: Newtype PlutusAppId _

derive instance eqPlutusAppId :: Eq PlutusAppId

derive instance ordPlutusAppId :: Ord PlutusAppId

derive instance genericPlutusAppId :: Generic PlutusAppId _

-- note we need to encode this type, not to communicate with the PAB (we have the `ContractInstanceId`
-- for that), but to save `WalletData` to local storage
instance encodePlutusAppId :: Encode PlutusAppId where
  encode value = genericEncode defaultOptions value

instance decodePlutusAppId :: Decode PlutusAppId where
  decode value = genericDecode defaultOptions value

-- FIXME: move these types into Marlowe.Semantics and Marlowe.Client
-- `MarloweParams` are used to identify a Marlowe contract in the PAB, and the wallet
-- companion contract state is a `Map MarloweParams MarloweData`. We are not currently
-- generating PureScript types to match the Haskell `MarloweParams` and `MarloweData`
-- types (side note: perhaps we should be). We have a `CurrencySymbol` type in
-- `Marlowe.Semantics`, but it is just an alias for String. We could use that here for
-- the `rolesCurrency` value, and convert using its Bridge instance when sharing data
-- with the PAB. However, we currently don't need to do anything with `MarloweParams` on
-- the frontend except save them and send them back to the PAB (to join a contract that
-- is already running), so it is simpler just to use the generated type in this case.
type MarloweParams
  = { rolePayoutValidatorHash :: ValidatorHash
    , rolesCurrency :: CurrencySymbol
    }

type ValidatorHash
  = String

type MarloweData
  = { marloweContract :: Contract
    , marloweState :: State
    }

-- This is the observable state of the `MarloweFollower`. The `MarloweParams` identify the
-- the Marlowe contract on the blockchain, the `MarloweData` represents the initial contract
-- and state, and the array of `TransactionInput`s records all the transactions of the
-- contract so far.  The value is `None` when the app is first activated, before the "follow"
-- endpoint has been called (and the PAB has had time to settle).
type ContractHistory
  = { chParams :: Maybe (Tuple MarloweParams MarloweData)
    , chHistory :: Array TransactionInput
    }
