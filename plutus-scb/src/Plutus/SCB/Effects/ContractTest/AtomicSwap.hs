{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
module Plutus.SCB.Effects.ContractTest.AtomicSwap(
    AtomicSwapParams(..),
    AtomicSwapError(..),
    AsAtomicSwapError(..),
    AtomicSwapSchema,
    atomicSwap
    ) where

import           Control.Lens
import           Control.Monad                                   (void)
import           Data.Aeson                                      (FromJSON, ToJSON)
import           GHC.Generics                                    (Generic)
import           IOTS                                            (IotsType)
import           Language.PlutusTx.Coordination.Contracts.Escrow (EscrowParams (..))
import qualified Language.PlutusTx.Coordination.Contracts.Escrow as Escrow
import           Schema                                          (ToSchema)

import           Language.Plutus.Contract
import           Ledger                                          (PubKey, Slot, Value)
import qualified Ledger

-- | Describes an exchange of two
--   'Value' amounts between two parties
--   identified by public keys
data AtomicSwapParams =
    AtomicSwapParams
        { value1   :: Value -- ^ The amount paid to the hash of 'pubKey1'
        , value2   :: Value -- ^ The amount paid to the hash of 'pubKey2'
        , pubKey1  :: PubKey -- ^ The first party in the atomic swap
        , pubKey2  :: PubKey -- ^ The second party in the atomic swap
        , deadline :: Slot -- ^ Last slot in which the swap can be executed.
        }
        deriving stock (Eq, Show, Generic)
        deriving anyclass (ToJSON, FromJSON, IotsType, ToSchema)

mkEscrowParams :: AtomicSwapParams -> EscrowParams t
mkEscrowParams AtomicSwapParams{value1,value2,pubKey1,pubKey2,deadline} =
    EscrowParams
        { escrowDeadline = deadline
        , escrowTargets =
                [ Escrow.payToPubKeyTarget (Ledger.pubKeyHash pubKey1) value1
                , Escrow.payToPubKeyTarget (Ledger.pubKeyHash pubKey2) value2
                ]
        }

type AtomicSwapSchema =
    BlockchainActions
        .\/ Endpoint "atomic-swap" AtomicSwapParams

data AtomicSwapError =
    EscrowError Escrow.EscrowError
    | OtherAtomicSwapError ContractError
    | NotInvolvedError PubKey AtomicSwapParams -- ^ When the wallet's public key doesn't match either of the two keys specified in the 'AtomicSwapParams'
    deriving (Show)

makeClassyPrisms ''AtomicSwapError
instance AsContractError AtomicSwapError where
    _ContractError = _OtherAtomicSwapError

-- | Perform the atomic swap. Needs to be called by both of the two parties
--   involved.
atomicSwap :: Contract AtomicSwapSchema AtomicSwapError ()
atomicSwap = do
    p <- endpoint @"atomic-swap"

    let params = mkEscrowParams p
        go pk
            | pk == pubKey1 p =
                -- there are two paying transactions and one redeeming transaction.
                -- The redeeming tx is submitted by party 1.
                -- TODO: Change 'payRedeemRefund' to check before paying into the
                -- address, so that the last paying transaction can also be the
                -- redeeming transaction.
                void $ mapError EscrowError (Escrow.payRedeemRefund params (value2 p))
            | pk == pubKey2 p =
                void $ mapError EscrowError (Escrow.pay (Escrow.scriptInstance params) params (value1 p)) >>= awaitTxConfirmed
            | otherwise = throwError (NotInvolvedError pk p)

    ownPubKey >>= go
