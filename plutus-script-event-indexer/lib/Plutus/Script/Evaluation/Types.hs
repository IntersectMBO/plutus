{-# LANGUAGE StrictData       #-}
{-# LANGUAGE TypeApplications #-}

module Plutus.Script.Evaluation.Types (
  Checkpoint (..),
  StreamerState (..),
  ScriptM,
  Block,
)
where

import Cardano.Api (EpochSlots (EpochSlots))
import Cardano.Api qualified as Cardano
import Codec.Serialise qualified as CBOR
import Codec.Serialise.Decoding qualified as CBOR
import Codec.Serialise.Encoding qualified as CBOR
import Control.Monad.Trans.State (StateT)
import Data.Proxy (Proxy (Proxy))
import Data.Word (Word64)
import Ouroboros.Consensus.Cardano.Block (CardanoCodecConfig)
import Ouroboros.Consensus.Cardano.Node (protocolClientInfoCardano)
import Ouroboros.Consensus.Node.ProtocolInfo (ProtocolClientInfo (pClientInfoCodecConfig))
import PlutusLedgerApi.Test.EvaluationEvent (ScriptEvaluationEvent)

-- | A checkpoint from which the streamer can resume.
data Checkpoint = Checkpoint
  { cChainPoint  :: Cardano.ChainPoint
  , cLedgerState :: Cardano.LedgerState
  }

codecConfig :: CardanoCodecConfig e
codecConfig =
  pClientInfoCodecConfig (protocolClientInfoCardano (EpochSlots 21600))

instance CBOR.Serialise Checkpoint where
  encode (Checkpoint chainPoint ledgerState) =
    mconcat
      [ CBOR.encodeListLen 2
      , encodeChainPoint chainPoint
      , Cardano.encodeLedgerState codecConfig ledgerState
      ]
  decode = do
    CBOR.decodeListLenOf 2
    Checkpoint <$> decodeChainPoint <*> Cardano.decodeLedgerState codecConfig

encodeChainPoint :: Cardano.ChainPoint -> CBOR.Encoding
encodeChainPoint p = CBOR.encode $ case p of
  Cardano.ChainPointAtGenesis  -> Nothing
  Cardano.ChainPoint slot hash -> Just (slot, Cardano.serialiseToRawBytes hash)

decodeChainPoint :: CBOR.Decoder s Cardano.ChainPoint
decodeChainPoint =
  CBOR.decode >>= \case
    Nothing -> pure Cardano.ChainPointAtGenesis
    Just (slot, hashRawBytes) ->
      either
        (\err -> fail ("decodeChainPoint is unable to decode block hash: " <> show err))
        (pure . Cardano.ChainPoint slot)
        ( Cardano.deserialiseFromRawBytes
            (Cardano.proxyToAsType (Proxy @(Cardano.Hash Cardano.BlockHeader)))
            hashRawBytes
        )

-- | State we maintain when consuming the stream of ledger state and events
data StreamerState = StreamerState
  { ssCount        :: Word64
  , ssV1CostParams :: Maybe [Integer]
  , ssV2CostParams :: Maybe [Integer]
  , ssEvents       :: [ScriptEvaluationEvent]
  }

type ScriptM = StateT StreamerState IO

type Block = Cardano.BlockInMode
