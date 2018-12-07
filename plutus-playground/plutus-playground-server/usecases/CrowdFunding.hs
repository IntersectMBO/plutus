-- | Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction. This is, of course, limited by the maximum
-- number of inputs a transaction can have.
module Language.PlutusTx.Coordination.Contracts.CrowdFunding where

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Prelude    as P
import           Ledger
import           Ledger.Validation
import           Playground.Contract
import           Wallet

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Height
    , campaignTarget             :: Value
    , campaignCollectionDeadline :: Height
    , campaignOwner              :: CampaignActor
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

type CampaignActor = PubKey

PlutusTx.makeLift ''Campaign

data CampaignAction = Collect | Refund
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''CampaignAction

-- | Contribute funds to the campaign (contributor)
--
contribute :: Campaign -> Value -> MockWallet ()
contribute cmp value = do
    _ <- if value <= 0 then throwOtherError "Must contribute a positive value" else pure ()
    ownPK <- ownPubKey
    let ds = DataScript (Ledger.lifted ownPK)
    tx <- payToScript (campaignAddress cmp) value ds
    logMsg "Submitted contribution"

    register (refundTrigger cmp) (refundHandler (Ledger.hashTx tx) cmp)
    logMsg "Registered refund trigger"

-- | Register a [[EventHandler]] to collect all the funds of a campaign
--
scheduleCollection :: Campaign -> MockWallet ()
scheduleCollection cmp = register (collectFundsTrigger cmp) (EventHandler (\_ -> do
        logMsg "Collecting funds"
        let redeemerScript = Ledger.RedeemerScript (Ledger.lifted Collect)
        collectFromScript (contributionScript cmp) redeemerScript))

-- | The address of a [[Campaign]]
campaignAddress :: Campaign -> Ledger.Address'
campaignAddress = Ledger.scriptAddress . contributionScript

-- | The validator script that determines whether the campaign owner can
--   retrieve the funds or the contributors can claim a refund.
--
--   Assume there is a campaign `c :: Campaign` with two contributors
--   (identified by public key pc_1 and pc_2) and one campaign owner (pco).
--   Each contributor creates a transaction, t_1 and t_2, whose outputs are
--   locked by the scripts `contributionScript c pc_1` and `contributionScript
--   c pc_1` respectively.
--   There are two outcomes for the campaign.
--   1. Campaign owner collects the funds from both contributors. In this case
--      the owner creates a single transaction with two inputs, referring to
--      t_1 and t_2. Each input contains the script `contributionScript c`
--      specialised to a contributor. This case is covered by the
--      `Collect` branch below.
--   2. Refund. In this case each contributor creates a transaction with a
--      single input claiming back their part of the funds. This case is
--      covered by the `Refund` branch.
contributionScript :: Campaign -> ValidatorScript
contributionScript cmp  = ValidatorScript val where
    val = Ledger.applyScript mkValidator (Ledger.lifted cmp)
    mkValidator = Ledger.fromPlcCode $$(PlutusTx.plutus [|| (\Campaign{..} (act :: CampaignAction) (con :: CampaignActor) (p :: PendingTx ValidatorHash) ->
        let

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $$(PlutusTx.and)

            PendingTx ps outs _ _ (Height h) _ _ = p

            deadline :: Int
            deadline = let Height h' = campaignDeadline in h'

            collectionDeadline :: Int
            collectionDeadline = let Height h' = campaignCollectionDeadline in h'

            target :: Int
            target = let Value v = campaignTarget in v

            -- | The total value of all contributions
            totalInputs :: Int
            totalInputs =
                let v (PendingTxIn _ _ (Value vl)) = vl in
                $$(P.foldr) (\i total -> total + v i) 0 ps

            isValid = case act of
                Refund -> -- the "refund" branch
                    let

                        contributorTxOut :: PendingTxOut -> Bool
                        contributorTxOut o = case $$(pubKeyOutput) o of
                            Nothing -> False
                            Just pk -> $$(eqPubKey) pk con

                        -- Check that all outputs are paid to the public key
                        -- of the contributor (this key is provided as the data script `con`)
                        contributorOnly = $$(P.all) contributorTxOut outs

                        refundable = h > collectionDeadline && contributorOnly && $$(txSignedBy) p con

                    in refundable
                Collect -> -- the "successful campaign" branch
                    let
                        payToOwner = h > deadline && h <= collectionDeadline && totalInputs >= target && $$(txSignedBy) p campaignOwner
                    in payToOwner
        in
        if isValid then () else $$(P.error) ()) ||])

-- | An event trigger that fires when a refund of campaign contributions can be claimed
refundTrigger :: Campaign -> EventTrigger
refundTrigger c = andT
    (fundsAtAddressT (campaignAddress c) (GEQ 1))
    (blockHeightT (GEQ (succ (campaignCollectionDeadline c))))

-- | An event trigger that fires when the funds for a campaign can be collected
collectFundsTrigger :: Campaign -> EventTrigger
collectFundsTrigger c = andT
    (fundsAtAddressT (campaignAddress c) (GEQ (campaignTarget c)))
    (blockHeightT (Interval (campaignDeadline c) (campaignCollectionDeadline c)))

-- | Claim a refund of our campaign contribution
refundHandler :: TxId' -> Campaign -> EventHandler MockWallet
refundHandler txid cmp = EventHandler (\_ -> do
    logMsg "Claiming refund"
    let validatorScript = contributionScript cmp
        redeemerScript  = Ledger.RedeemerScript (Ledger.lifted Refund)
    collectFromScriptTxn validatorScript redeemerScript txid)

$(mkFunction 'scheduleCollection)
$(mkFunction 'contribute)
