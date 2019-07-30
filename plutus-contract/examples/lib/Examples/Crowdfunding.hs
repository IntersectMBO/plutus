{-# LANGUAGE ApplicativeDo      #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE TypeOperators      #-}
-- | Contract interface for the crowdfunding contract
module Examples.Crowdfunding(
      Campaign(..)
    , crowdfunding
    , theCampaign
    , CF.campaignAddress
    ) where

import           Control.Applicative                                   (Alternative (..))
import           Control.Lens                                          ((&), (.~), (^.))
import           Control.Monad                                         (void)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Tx                           (collectFromScript, collectFromScriptFilter,
                                                                        inputs, payToScript, validityRange)
import           Language.PlutusTx.Coordination.Contracts.CrowdFunding (Campaign (..))
import qualified Language.PlutusTx.Coordination.Contracts.CrowdFunding as CF

import           Ledger                                                (PubKey, Value)
import qualified Ledger                                                as L
import qualified Ledger.Ada                                            as Ada
import           Ledger.Scripts                                        (DataScript (..))

import qualified Wallet.Emulator                                       as Emulator

crowdfunding :: ContractActions r => Contract r ()
crowdfunding = contribute theCampaign <|> scheduleCollection theCampaign

theCampaign :: Campaign
theCampaign = Campaign
    { campaignDeadline = 20
    , campaignTarget   = Ada.adaValueOf 20
    , campaignCollectionDeadline = 30
    , campaignOwner = Emulator.walletPubKey (Emulator.Wallet 1)
    }

contribute :: ContractActions r => Campaign -> Contract r ()
contribute cmp = do
    (ownPK :: PubKey, contribution :: Value) <- endpoint "contribute"
    let ds = DataScript (L.lifted ownPK)
        tx = payToScript contribution (CF.campaignAddress cmp) ds
                & validityRange .~ L.interval 1 (campaignDeadline cmp)
    writeTx tx

    utxo <- watchAddressUntil (CF.campaignAddress cmp) (CF.campaignCollectionDeadline cmp)
    -- check if we are eligible for a refund

    -- This is a bit fiddly since we don't know the transaction ID of 'tx'.
    -- So we use `collectFromScriptFilter` to collect only those outputs
    -- whose data script is our own public key (in 'ds')
    let flt _ txOut = L.txOutData txOut == Just ds
        tx' = collectFromScriptFilter flt utxo (CF.contributionScript cmp) (L.RedeemerScript (L.lifted CF.Refund))
                & validityRange .~ CF.refundRange cmp
    if not . null $ tx' ^. inputs
    then void (writeTx tx')
    else pure ()

scheduleCollection :: ContractActions r => Campaign -> Contract r ()
scheduleCollection cmp = do
    () <- endpoint "schedule collection"
    let trg = fst <$> both
                (fundsAtAddressGt (CF.campaignAddress cmp) (campaignTarget cmp))
                (awaitSlot (CF.campaignDeadline cmp))
    void $ timeout (CF.campaignCollectionDeadline cmp) $ do
        outxo <- trg
        let
            redeemerScript = L.RedeemerScript (L.lifted CF.Collect)
            tx = collectFromScript outxo (CF.contributionScript cmp) redeemerScript
                    & validityRange .~ CF.collectionRange cmp
        writeTx tx
