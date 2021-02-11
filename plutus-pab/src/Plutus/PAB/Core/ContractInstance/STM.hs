{-

Types and functions for contract instances that communicate with the outside
world via STM.

-}
module Plutus.PAB.Core.ContractInstance.STM(
    OpenEndpoint(..)
    , BlockchainEnv(..)
    , InstanceState(..)
    ) where

{- Note [Contract instance thread model]

FIXME

-}

-- | An open endpoint that can be responded to.
data OpenEndpoint =
        OpenEndpoint
            { oepName     :: String -- ^ Name of the endpoint
            , oepMeta     :: Maybe Value -- ^ Metadata that was provided by the contract
            , oepResponse :: TVar Value -- ^ A place to write the response to.
            }

-- | Data about the blockchain that contract instances
--   may be interested in.
data BlockchainEnv =
    BlockchainEnv
        { envLastSlot  :: TVar Slot -- ^ The current slot.
        , envLastBlock :: TVar [Tx] -- ^ Last block that was validated
        -- TODO: Add rollbacks when we get them from
        --       the mock node
        }

-- | The state of an active contract instance
data InstanceState =
    InstanceState
        { issEndpoints :: TVar (Map String OpenEndpoint)
        , issLogs      :: TChan InstanceLogMsg
        }
