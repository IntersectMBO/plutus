{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- | Quoted expressions for generating validation data
module Spec.TH(
    pendingTxVesting,
    pendingTxCrowdfunding
    ) where

import           Language.Haskell.TH                                 (Exp, Q)
import qualified Language.Plutus.CoreToPLC.Primitives                as Prim
import           Language.Plutus.Runtime                             (Hash (..), Height, PendingTx (..),
                                                                      PendingTxIn (..), PendingTxOut (..),
                                                                      PendingTxOutRef (..), PendingTxOutType (..),
                                                                      Signature, Value)
import           Wallet.API                                          (PubKey (..))

import           Language.Plutus.Coordination.Contracts.CrowdFunding (CampaignActor)
import           Language.Plutus.Coordination.Contracts.Vesting      (VestingData (..))

-- | Create a `PendingTx () VestingData` from a block height and a value
--   (of funds taken out of the scheme)
pendingTxVesting :: Q Exp
pendingTxVesting = [| \(h :: Height) (out :: Value) ->
    let total = 600
        hash = 1123 -- stand-in for a transaction hash
        rest  = total - out
    in PendingTx {
        pendingTxCurrentInput = (PendingTxIn (PendingTxOutRef 100 0 []) (), total),
        pendingTxOtherInputs  = []::[(PendingTxIn (), Value)],
        pendingTxOutputs      = (PendingTxOut out Nothing (PubKeyTxOut (PubKey 1))::(PendingTxOut VestingData)):(PendingTxOut rest (Just (VestingData hash out)) DataTxOut::(PendingTxOut VestingData)):([]::[PendingTxOut VestingData]),
        pendingTxForge        = 0,
        pendingTxFee          = 0,
        pendingTxBlockHeight  = h,
        pendingTxSignatures   = []
        } |]

-- | Create a `PendingTx () CampaignActor` from a block height, transaction signatures,
--    and one or two inputs with their respective signatures.
pendingTxCrowdfunding :: Q Exp
pendingTxCrowdfunding = [| \(h :: Height) (txSigs :: [Signature]) ((v1, sig1)::(Value,[Signature])) (v2::Maybe (Value, [Signature])) ->
    let i1 = (PendingTxIn (PendingTxOutRef 100 1 sig1) (), v1)
        i2 = case v2 of
                Just (v2', sig2) -> (PendingTxIn (PendingTxOutRef 200 1 sig2) (), v2'):[]
                Nothing          -> []::[(PendingTxIn (), Value)]
    in PendingTx {
        pendingTxCurrentInput = i1,
        pendingTxOtherInputs  = i2,
        pendingTxOutputs      = []::[PendingTxOut CampaignActor],
        pendingTxForge        = 0,
        pendingTxFee          = 0,
        pendingTxBlockHeight  = h,
        pendingTxSignatures   = txSigs
        }
    |]
