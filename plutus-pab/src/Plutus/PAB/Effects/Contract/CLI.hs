{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeFamilies       #-}
{-

'ContractEffect' handler for contracts that use the CLI
interface.

-}
module Plutus.PAB.Effects.Contract.CLI(
    ContractExe(..)
    ) where

import           Cardano.BM.Data.Tracer.Extras           (StructuredLog (..))
import           Data.Aeson                              (FromJSON (..), ToJSON (..))
import qualified Data.HashMap.Strict                     as HM
import           Data.Text.Prettyprint.Doc               (Pretty, pretty, viaShow, (<+>))
import           GHC.Generics                            (Generic)
import           Plutus.PAB.Effects.Contract             (PABContract (..))
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)

instance PABContract ContractExe where
    type ContractDef ContractExe = ContractExe
    type State ContractExe = PartiallyDecodedResponse ContractPABRequest

    requests = error "FIXME"

newtype ContractExe =
    ContractExe
        { contractPath :: FilePath
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance StructuredLog ContractExe where
    toStructuredLog e = HM.singleton "contract" (toJSON e)

instance Pretty ContractExe where
    pretty ContractExe {contractPath} = "Path:" <+> pretty contractPath


-- data ExternalProcessContract

-- instance PABContract ExternalProcessContract where

    -- type ContractInput ExternalProcessContract = State.ContractRequest JSON.Value
    -- type ContractState

-- type Request t = State.ContractRequest (Input t)

-- -- | The state of a contract instance.
-- type State t = State.ContractResponse (ObsState t) (Err t) (IntState t) (OpenRequest t)
