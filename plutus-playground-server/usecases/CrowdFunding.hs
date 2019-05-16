-- | Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction.
--
-- Note [Transactions in the crowdfunding campaign] explains the structure of
-- this contract on the blockchain.
import qualified Language.PlutusTx            as PlutusTx
import qualified Ledger.Interval              as Interval
import           Ledger.Slot                  (SlotRange)
import qualified Ledger.Slot                  as Slot
import qualified Language.PlutusTx.Prelude    as P
import           Ledger
import           Ledger.Validation           as V
import           Ledger.Value                (Value)
import qualified Ledger.Value.TH             as VTH
import           Playground.Contract
import           Wallet                       as W
import qualified Wallet.Emulator              as EM

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Slot
    -- ^ The date by which the campaign target has to be met
    , campaignTarget             :: Value
    -- ^ Target amount of funds
    , campaignCollectionDeadline :: Slot
    -- ^ The date by which the campaign owner has to collect the funds
    , campaignOwner              :: PubKey
    -- ^ Public key of the campaign owner. This key is entitled to retrieve the
    --   funds if the campaign is successful.
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''Campaign


-- | Construct a 'Campaign' value from the campaign parameters,
--   using the wallet's public key.
mkCampaign :: Slot -> Value -> Slot -> Wallet -> Campaign
mkCampaign ddl target collectionDdl ownerWallet =
    Campaign
        { campaignDeadline = ddl
        , campaignTarget   = target
        , campaignCollectionDeadline = collectionDdl
        , campaignOwner = EM.walletPubKey ownerWallet
        }

-- | The 'SlotRange' during which the funds can be collected
collectionRange :: Campaign -> SlotRange
collectionRange cmp =
    W.interval (campaignDeadline cmp) (campaignCollectionDeadline cmp)

-- | The 'SlotRange' during which a refund may be claimed
refundRange :: Campaign -> SlotRange
refundRange cmp =
    W.intervalFrom (campaignCollectionDeadline cmp)

-- | Action that can be taken by the participants in this contract. A value of
--   `CampaignAction` is provided as the redeemer. The validator script then
--   checks if the conditions for performing this action are met.
--
data CampaignAction = Collect | Refund
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''CampaignAction

-- | The validator script that determines whether the campaign owner can
--   retrieve the funds or the contributors can claim a refund.
--
contributionScript :: Campaign -> ValidatorScript
contributionScript cmp  = ValidatorScript val where
    val = Ledger.applyScript mkValidator (Ledger.lifted cmp)
    mkValidator = $$(Ledger.compileScript [||

        -- The validator script is a function of four arguments:
        -- 1. The 'Campaign' definition. This argument is provided by the Plutus client, using 'Ledger.applyScript'.
        --    As a result, the 'Campaign' definition is part of the script address, and different campaigns have different addresses.
        --    The Campaign{..} syntax means that all fields of the 'Campaign' value are in scope (for example 'campaignDeadline' in l. 70).
        --    See note [RecordWildCards].
        --
        -- 2. A 'PubKey'. This is the data script. It is provided by the producing transaction (the contribution)
        --
        -- 3. A 'CampaignAction'. This is the redeemer script. It is provided by the redeeming transaction.
        --
        -- 4. A 'PendingTx value. It contains information about the current transaction and is provided by the slot leader.
        --    See note [PendingTx]
        \Campaign{..} (con :: PubKey) (act :: CampaignAction) (p :: PendingTx) ->
            let

                -- In Haskell we can define new operators. We import
                -- `P.and` from the PlutusTx prelude here so that we can use it
                -- in infix position rather than prefix (which would require a
                -- lot of additional brackets)
                infixr 3 &&
                (&&) :: Bool -> Bool -> Bool
                (&&) = P.and

                signedBy :: PendingTx -> PubKey -> Bool
                signedBy = V.txSignedBy

                -- We pattern match on the pending transaction `p` to get the
                -- information we need:
                -- `ps` is the list of inputs of the transaction
                -- `outs` is the list of outputs
                -- `slFrom` is the beginning of the validation interval
                -- `slTo` is the end of the validation interval
                PendingTx ps outs _ _ _ range _ _ = p

                collRange :: SlotRange
                collRange = Interval.interval campaignDeadline campaignCollectionDeadline

                refndRange :: SlotRange
                refndRange = Interval.from campaignCollectionDeadline

                -- `totalInputs` is the sum of the values of all transaction
                -- inputs. We use `foldr` from the Prelude to go through the
                -- list and sum up the values.
                totalInputs :: Value
                totalInputs =
                    let v (PendingTxIn _ _ vl) = vl in
                    P.foldr (\i total -> VTH.plus total (v i)) VTH.zero ps

                isValid = case act of
                    Refund -> -- the "refund" branch
                        let

                            contributorTxOut :: PendingTxOut -> Bool
                            contributorTxOut o = case pubKeyOutput o of
                                Nothing -> False
                                Just pk -> eqPubKey pk con

                            -- Check that all outputs are paid to the public key
                            -- of the contributor (this key is provided as the data script `con`)
                            contributorOnly = P.all contributorTxOut outs

                            refundable =
                                Slot.contains refndRange range
                                && contributorOnly && p `signedBy` con

                        in refundable
                    Collect -> -- the "successful campaign" branch
                        let
                            payToOwner =
                                Slot.contains collRange range
                                && VTH.geq totalInputs campaignTarget
                                && p `signedBy` campaignOwner
                        in payToOwner
            in
            if isValid then () else P.error () ||])

-- | The address of a [[Campaign]]
campaignAddress :: Campaign -> Ledger.Address
campaignAddress = Ledger.scriptAddress . contributionScript

-- | Contribute funds to the campaign (contributor)
--
contribute :: MonadWallet m => Slot -> Value -> Slot -> Wallet -> Value -> m ()
contribute deadline target collectionDeadline ownerWallet value = do
    let cmp = mkCampaign deadline target collectionDeadline ownerWallet
    ownPK <- ownPubKey
    let ds = DataScript (Ledger.lifted ownPK)
        range = W.interval 1 (campaignDeadline cmp)

    -- `payToScript` is a function of the wallet API. It takes a campaign
    -- address, value, and data script, and generates a transaction that
    -- pays the value to the script. `tx` is bound to this transaction. We need
    -- to hold on to it because we are going to use it in the refund handler.
    -- If we were not interested in the transaction produced by `payToScript`
    -- we could have used `payeToScript_`, which has the same effect but
    -- discards the result.
    tx <- payToScript range (campaignAddress cmp) value ds

    logMsg "Submitted contribution"

    -- `register` adds a blockchain event handler on the `refundTrigger`
    -- event. It instructs the wallet to start watching the addresses mentioned
    -- in the trigger definition and run the handler when the refund condition
    -- is true.
    register (refundTrigger value cmp) (refundHandler (Ledger.hashTx tx) cmp)

    logMsg "Registered refund trigger"

-- | Register a [[EventHandler]] to collect all the funds of a campaign
--
scheduleCollection :: MonadWallet m => Slot -> Value -> Slot -> Wallet -> m ()
scheduleCollection deadline target collectionDeadline ownerWallet = do
    let cmp = mkCampaign deadline target collectionDeadline ownerWallet
    register (collectFundsTrigger cmp) (EventHandler (\_ -> do
        logMsg "Collecting funds"
        let redeemerScript = Ledger.RedeemerScript (Ledger.lifted Collect)
            range = collectionRange cmp
        collectFromScript range (contributionScript cmp) redeemerScript))

-- | An event trigger that fires when a refund of campaign contributions can be claimed
refundTrigger :: Value -> Campaign -> EventTrigger
refundTrigger vl c = andT
    (fundsAtAddressT (campaignAddress c) (W.intervalFrom vl))
    (slotRangeT (refundRange c))

-- | An event trigger that fires when the funds for a campaign can be collected
collectFundsTrigger :: Campaign -> EventTrigger
collectFundsTrigger c = andT
    (fundsAtAddressT (campaignAddress c) (W.intervalFrom (campaignTarget c)))
    (slotRangeT (collectionRange c))

-- | Claim a refund of our campaign contribution
refundHandler :: MonadWallet m => TxId -> Campaign -> EventHandler m
refundHandler txid cmp = EventHandler (\_ -> do
    logMsg "Claiming refund"
    let validatorScript = contributionScript cmp
        redeemerScript  = Ledger.RedeemerScript (Ledger.lifted Refund)

    -- `collectFromScriptTxn` generates a transaction that spends the unspent
    -- transaction outputs at the address of the validator scripts, *but* only
    -- those outputs that were produced by the transaction `txid`. We use it
    -- here to ensure that we don't attempt to claim back other contributors'
    -- funds (if we did that, the validator script would fail and the entire
    -- transaction would be invalid).
    collectFromScriptTxn (refundRange cmp) validatorScript redeemerScript txid)

$(mkFunctions ['scheduleCollection, 'contribute])

{- note [Transactions in the crowdfunding campaign]

Assume there is a campaign `c :: Campaign` with two contributors
(identified by public key `pc_1` and `pc_2`) and one campaign owner (pco).
Each contributor creates a transaction, `t_1` and `t_2`, whose outputs are
locked by the scripts `contributionScript c pc_1` and `contributionScript
c pc_1` respectively.

There are two outcomes for the campaign.

1. Campaign owner collects the funds from both contributors. In this case
   the owner creates a single transaction with two inputs, referring to
   `t_1` and `t_2`. Each input contains the script `contributionScript c`
   specialised to a contributor. The redeemer script of this transaction contains the value `Collect`, prompting the validator script to check the
   branch for `Collect`.

2. Refund. In this case each contributor creates a transaction with a
   single input claiming back their part of the funds. This case is
   covered by the `Refund` branch, and its redeemer script is the `Refund` action.

In both cases, the validator script is run twice. In the first case there is a single transaction consuming both inputs. In the second case there are two different transactions that may happen at different times.

-}

{- note [RecordWildCards]

We can use the syntax "Campaign{..}" here because the 'RecordWildCards'
extension is enabled automatically by the Playground backend.

The extension is documented here:
* https://downloads.haskell.org/~ghc/7.2.1/docs/html/users_guide/syntax-extns.html

A list of extensions that are enabled by default for the Playground can be found here:
* https://github.com/input-output-hk/plutus/blob/b0f49a0cc657cd1a4eaa4af72a6d69996b16d07a/plutus-playground/plutus-playground-server/src/Playground/Interpreter.hs#L44

-}

{- note [PendingTx]

This part of the API (the PendingTx argument) is experimental and subject to change.

-}
