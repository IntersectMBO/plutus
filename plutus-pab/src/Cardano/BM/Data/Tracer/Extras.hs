{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
module Cardano.BM.Data.Tracer.Extras(
    mkObjectStr
    , PrettyToObject(..)
    , StructuredLog(..)
    , Tagged(Tagged)
    ) where

import           Cardano.BM.Data.Tracer                  (ToObject (..))
import           Data.Aeson                              (ToJSON (..), Value (String))
import           Data.HashMap.Strict                     (HashMap)
import qualified Data.HashMap.Strict                     as HM
import           Data.Proxy                              (Proxy (..))
import           Data.Tagged                             (Tagged (Tagged))
import           Data.Text                               (Text)
import qualified Data.Text                               as Text
import           Data.Text.Prettyprint.Doc               (Pretty (..), defaultLayoutOptions, layoutPretty)
import qualified Data.Text.Prettyprint.Doc.Render.Text   as Render
import           Data.UUID                               (UUID)
import           GHC.TypeLits                            (KnownSymbol, symbolVal)
import           Ledger.Tx                               (Tx)
import qualified Ledger.Value                            as V
import           Plutus.PAB.Events.Contract              (ContractInstanceId, IterationID)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse (..))
import           Wallet.Emulator.LogMessages             (RequestHandlerLogMsg, TxBalanceMsg)
import           Wallet.Types                            (EndpointDescription)

-- | Deriving 'ToObject' from 'Pretty'
newtype PrettyToObject a = PrettyToObject { unPrettyToObject :: a }

instance Pretty a => ToObject (PrettyToObject a) where
    toObject _ = HM.singleton "string" . String . Render.renderStrict . layoutPretty defaultLayoutOptions . pretty . unPrettyToObject

toStructuredLog' :: forall s a. (KnownSymbol s, ToJSON a) => Tagged s a -> HashMap Text Value
toStructuredLog' (Tagged a) =
    let k = Text.pack (symbolVal (Proxy @s))
        v = toJSON a
    in HM.singleton k v

-- | Types that can be turned into structured log messages
class StructuredLog a where
    toStructuredLog :: a -> HashMap Text Value

instance StructuredLog () where
    toStructuredLog _ = HM.empty

instance (StructuredLog a, StructuredLog b) =>
    StructuredLog (a, b) where
        toStructuredLog (a, b) = HM.union (toStructuredLog a) (toStructuredLog b)

instance (StructuredLog a, StructuredLog b, StructuredLog c) =>
    StructuredLog (a, b, c) where
        toStructuredLog (a, b, c) = HM.union (toStructuredLog a) (toStructuredLog (b, c))

instance (StructuredLog a, StructuredLog b, StructuredLog c, StructuredLog d) =>
    StructuredLog (a, b, c, d) where
        toStructuredLog (a, b, c, d) = HM.union (toStructuredLog a) (toStructuredLog (b, c, d))

instance (StructuredLog a, StructuredLog b) =>
    StructuredLog (Either a b) where
        toStructuredLog = either toStructuredLog toStructuredLog

instance StructuredLog a => StructuredLog (Maybe a) where
    toStructuredLog = maybe mempty toStructuredLog

deriving via (Tagged "contract_instance" ContractInstanceId) instance StructuredLog ContractInstanceId
deriving via (Tagged "contract_instance_iteration" IterationID) instance StructuredLog IterationID
deriving via (Tagged "message" CheckpointLogMsg) instance StructuredLog CheckpointLogMsg
deriving via (Tagged "message" RequestHandlerLogMsg) instance StructuredLog RequestHandlerLogMsg
deriving via (Tagged "message" TxBalanceMsg) instance StructuredLog TxBalanceMsg
deriving via (Tagged "tx" Tx) instance StructuredLog Tx
deriving via (Tagged "uuid" UUID) instance StructuredLog UUID
deriving via (Tagged "request" (ContractRequest v)) instance ToJSON v => StructuredLog (ContractRequest v)
deriving via (Tagged "value" V.Value) instance StructuredLog V.Value
deriving via (Tagged "endpoint" EndpointDescription) instance StructuredLog EndpointDescription
instance ToJSON v => StructuredLog (PartiallyDecodedResponse v) where
    toStructuredLog PartiallyDecodedResponse{hooks, observableState} =
        HM.fromList [("hooks", toJSON hooks), ("state", toJSON observableState)]

instance (KnownSymbol s, ToJSON a) => StructuredLog (Tagged s a) where
    toStructuredLog = toStructuredLog'

-- | A structured log object with a textual description and additional fields.
mkObjectStr :: StructuredLog k => Text -> k -> HashMap Text Value
mkObjectStr str rest =
    HM.insert "string" (String str) (toStructuredLog rest)
