module Cardano.Api (
    -- * Type tags
    HasTypeProxy(..),
    AsType(..),
    HasTextEnvelope (..),
    SerialiseAsCBOR,
    TextEnvelopeType (..)
)
where

-- we need the following for
-- plutus-ledger
--  AsType,
--  HasTextEnvelope (textEnvelopeType),
--  HasTypeProxy (proxyToAsType),
--  SerialiseAsCBOR,
--  TextEnvelopeType (TextEnvelopeType)

import           Cardano.Api.HasTypeProxy
import           Cardano.Api.SerialiseCBOR
import           Cardano.Api.SerialiseTextEnvelope
