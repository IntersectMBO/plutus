module Marlowe.PAB
  ( transactionFee
  , contractCreationFee
  , PlutusAppId(..)
  ) where

import Prelude
import Data.BigInteger (BigInteger, fromInt)
import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.UUID (UUID)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)

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
