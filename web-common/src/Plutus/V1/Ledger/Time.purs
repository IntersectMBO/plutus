-- As 'POSIXTime' from 'Plutus.V1.Ledger.Time' has a custom 'FromJSON' and 'ToJSON'
-- instances, we declare the corresponding 'POSIXTime' PureScript type here since
-- the PSGenerator Generic instances won't match.
module Plutus.V1.Ledger.Time where

import Data.BigInteger (BigInteger, readBigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Iso')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Newtype (class Newtype)
import Foreign.Class (class Decode, class Encode, encode)
import Prelude

newtype POSIXTime
  = POSIXTime
  { getPOSIXTime :: BigInteger
  }

derive instance eqPOSIXTime :: Eq POSIXTime

instance showPOSIXTime :: Show POSIXTime where
  show x = genericShow x

instance encodePOSIXTime :: Encode POSIXTime where
  encode (POSIXTime { getPOSIXTime: value }) = encode value

instance decodePOSIXTime :: Decode POSIXTime where
  decode value = (\v -> POSIXTime { getPOSIXTime: v }) <$> readBigInteger value

derive instance genericPOSIXTime :: Generic POSIXTime _

derive instance newtypePOSIXTime :: Newtype POSIXTime _

--------------------------------------------------------------------------------
_POSIXTime :: Iso' POSIXTime { getPOSIXTime :: BigInteger }
_POSIXTime = _Newtype

--------------------------------------------------------------------------------
