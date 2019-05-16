{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Tutorial.Solutions0 where

import           Data.Foldable                (traverse_)
import qualified Language.PlutusTx            as P
import           Ledger                       (Address, DataScript(..), PubKey(..), RedeemerScript(..), Slot(..), TxId, ValidatorScript(..))
import qualified Ledger                       as L
import qualified Ledger.Ada.TH                as Ada
import           Ledger.Ada.TH                (Ada)
import qualified Ledger.Interval              as Interval
import qualified Ledger.Slot                  as Slot
import           Ledger.Validation            (PendingTx(..), PendingTxIn(..), PendingTxOut)
import qualified Ledger.Validation            as V
import           Wallet                       (WalletAPI(..), WalletDiagnostics(..), MonadWallet, EventHandler(..), EventTrigger)
import qualified Wallet                       as W
import           Prelude                      hiding ((&&))
import           GHC.Generics                 (Generic)

{-

  Solutions for the wallet API tutorials

-}

-- 1. Wallet API I (guessing game)


-- 1. Run traces for a successful game and a failed game in the Playground, and examine the logs after each trace.
-- (the logs should show the error message for the failed trace)
-- 2. Change the error case of the validator script to `($$(P.traceH) "WRONG!" ($$(P.error) ()))` and run the trace again with a wrong guess. Note how this time the log does not include the error message.
-- (there should be a failed transaction without log message)
-- 1. Look at the trace shown below. What will the logs say after running "Evaluate"?
-- Wallet 1's transaction attempts to unlock both outputs with the same redeemer ("plutus"). This fails for the second output (which expects "pluto"), making the entire transaction invalid.

-- 2. Wallet API II (crowdfunding)

-- 1. Run traces for successful and failed campaigns
--    In the logs for the succesful trace you should see the "collect funds"
--    trigger being activated after the `endDate` slot. (Make sure to include a
--    wait action to add some empty blocks). The trace of the failed campaign
--    should end with refunds being claimed after the `collectionDeadline` slot.

-- 2. Change the validator script to produce more detailed log messages using
--    `P.traceH`
--    The log messages are only printed when validation of the script output
--    fails. The triggers for both outcomes (successful campaign and refund)
--    are set up to ensure that they only submit valid transactions to the
--    chain. An easy way to get the handler code to produce an invalid
--    transaction is by changing the last line of `refundHandler` to
--
--    W.collectFromScript_ range (mkValidatorScript cmp) redeemer)
--
--    that is, to attempt to collect refunds for all contributions.

-- 3. Write a variation of the crowdfunding campaign that uses

-- ```
-- data Campaign = Campaign {
--       fundingTargets     :: [(Slot, Ada)],
--       campaignOwner      :: PubKey
--  }
-- ```

-- where `fundingTargets` is a list of slot numbers with associated Ada amounts. The campaign is successful if the funding target for one of the slots has been reached before that slot begins. For example, a campaign with
-- `Campaign [(Slot 20, Ada 100), (Slot 30, Ada 200)]` is successful if the contributions amount to 100 Ada or more by slot 20, or 200 Ada or more by slot 30.

-- SOLUTION
-- For this solution we use a `Campaign` type that also has the
-- `collectionDeadline` field from the original crowdfunding campaign (this was
-- on oversight on my part)
--
-- The remaining types are the same. We can re-use the code from the original
-- crowdfunder that deals with refunds. Only the code that deals with a
-- successful campaign needs to be changed. Below is the full contract. I added
-- comments where the code differs from the original.

data Campaign = Campaign {
      fundingTargets     :: [(Slot, Ada)],
      collectionDeadline :: Slot,
      campaignOwner      :: PubKey
 }

P.makeLift ''Campaign

data CampaignAction = Collect | Refund
P.makeLift ''CampaignAction

data Contributor = Contributor PubKey
P.makeLift ''Contributor

mkValidatorScript :: Campaign -> ValidatorScript
mkValidatorScript campaign = ValidatorScript val where
  val = L.applyScript mkValidator (L.lifted campaign)
  mkValidator = L.fromCompiledCode $$(P.compile [||
              \(c :: Campaign) (con :: Contributor) (act :: CampaignAction) (p :: PendingTx) ->
      let
        infixr 3 &&
        (&&) :: Bool -> Bool -> Bool
        (&&) = P.and


        signedBy :: PendingTx -> PubKey -> Bool
        signedBy = V.txSignedBy

        PendingTx ins outs _ _ _ txnValidRange _ _ = p
        -- p is bound to the pending transaction.

        Campaign targets collectionDeadline campaignOwner = c

        totalInputs :: Ada
        totalInputs =
              -- define a function "addToTotal" that adds the ada
              -- value of a 'PendingTxIn' to the total
              let addToTotal (PendingTxIn _ _ vl) total =
                      let adaVl = Ada.fromValue vl
                      in Ada.plus total adaVl

              -- Apply "addToTotal" to each transaction input,
              -- summing up the results
              in P.foldr addToTotal Ada.zero ins

        isValid = case act of
                    Refund ->
                        let
                            Contributor pkCon = con

                            contribTxOut :: PendingTxOut -> Bool
                            contribTxOut o =
                              case V.pubKeyOutput o of
                                Nothing -> False
                                Just pk -> V.eqPubKey pk pkCon

                            contributorOnly = P.all contribTxOut outs

                            refundable =
                              Slot.before collectionDeadline txnValidRange &&
                              contributorOnly &&
                              p `signedBy` pkCon

                        in refundable

                    -- START OF NEW CODE
                    Collect ->
                      let

                        -- | Check whether a given 'Slot' is after the current
                        --   transaction's valid range
                        isFutureSlot :: Slot -> Bool
                        isFutureSlot sl = Slot.after sl txnValidRange

                        -- | Return the smaller of two 'Ada' values
                        --   (NB this should be in the standard library)
                        minAda :: Ada -> Ada -> Ada
                        minAda l r = if Ada.lt l r then l else r

                        -- | Return the minimum of a list of 'Ada' values, if
                        --   it exists
                        minimumAda :: [Ada] -> Maybe Ada
                        minimumAda slts = case slts of
                                        []   -> Nothing
                                        x:xs -> Just (P.foldr minAda x xs)

                        -- | The list of 'targets' filtered to those targets
                        --   that are in the future
                        futureTargets :: [(Slot, Ada)]
                        futureTargets = P.filter (\(a, _) -> isFutureSlot a) targets

                        -- | The amount we have to exceed if we want to collect
                        --   all the contributions now. It is the smallest of
                        --   all target amounts that are in the future.
                        currentTarget :: Maybe Ada
                        currentTarget = minimumAda (P.map (\(_, a) -> a) futureTargets)

                        -- We may collect the contributions if the
                        -- 'currentTarget' is defined and the sum of all
                        -- inputs meets it.
                        targetMet =
                            case currentTarget of
                              Nothing -> False
                              Just a  -> Ada.geq totalInputs a

                      in
                        -- note that we don't need to check the pending
                        -- transaction's validity interval separately.
                        -- 'targetMet' is only true if the interval ends
                        -- before at least one of the targets.
                          targetMet &&
                          p `signedBy` campaignOwner

                            -- END OF NEW CODE
      in if isValid then () else (P.error ()) ||])

campaignAddress :: Campaign -> Address
campaignAddress cmp = L.scriptAddress (mkValidatorScript cmp)

mkDataScript :: PubKey -> DataScript
mkDataScript pk = DataScript (L.lifted (Contributor pk))

mkRedeemer :: CampaignAction -> RedeemerScript
mkRedeemer action = RedeemerScript (L.lifted (action))

refundHandler :: MonadWallet m => TxId -> Campaign -> EventHandler m
refundHandler txid cmp = EventHandler (\_ -> do
    W.logMsg "Claiming refund"
    currentSlot <- W.slot
    let redeemer  = mkRedeemer Refund
        range     = W.intervalFrom currentSlot
    W.collectFromScriptTxn range (mkValidatorScript cmp) redeemer txid)

refundTrigger :: Campaign -> EventTrigger
refundTrigger c = W.andT
    (W.fundsAtAddressT (campaignAddress c) (W.intervalFrom (Ada.toValue 1)))
    (W.slotRangeT (W.intervalFrom (collectionDeadline c)))

contribute :: MonadWallet m => Campaign -> Ada -> m ()
contribute cmp adaAmount = do
        pk <- W.ownPubKey
        let dataScript = mkDataScript pk
            amount = Ada.toValue adaAmount

        -- payToScript returns the transaction that was submitted
        -- (unlike payToScript_ which returns unit)
        tx <- W.payToScript W.defaultSlotRange (campaignAddress cmp) amount dataScript
        W.logMsg "Submitted contribution"

        -- L.hashTx gives the `TxId` of a transaction
        let txId = L.hashTx tx

        W.register (refundTrigger cmp) (refundHandler txId cmp)
        W.logMsg "Registered refund trigger"

{-

    We will define a collection trigger for each '(Slot, Ada)' entry in the
    'fundingTargets' list. This trigger fires if the specified amount has been
    contributed before the slot.

    That means we collect the funds as soon as the validator script allows it.

-}
mkCollectTrigger :: Address -> Slot -> Ada -> EventTrigger
mkCollectTrigger addr sl target = W.andT
    -- We use `W.intervalFrom` to create an open-ended interval that starts
    -- at the funding target.
    (W.fundsAtAddressT addr (W.intervalFrom (Ada.toValue target)))
    -- With `W.intervalTo` we create an interval from now to the target slot 'sl'
    (W.slotRangeT (W.intervalTo sl))

{-
    Each '(Slot, Ada)' entry in 'fundingTargets' also gets its own handler. In
    the handler we create a transaction that must be validated before the slot,
    using 'W.interval'
-}
collectionHandler :: MonadWallet m => Campaign -> Slot -> EventHandler m
collectionHandler cmp targetSlot = EventHandler (\_ -> do
    W.logMsg "Collecting funds"
    currentSlot <- W.slot
    let redeemerScript = mkRedeemer Collect
        range          = W.interval currentSlot targetSlot
    W.collectFromScript range (mkValidatorScript cmp) redeemerScript)

scheduleCollection :: MonadWallet m => Campaign -> m ()
scheduleCollection cmp =
    let
        addr = campaignAddress cmp
        ts = fundingTargets cmp
        regTarget (targetSlot, ada) = W.register (mkCollectTrigger addr targetSlot ada) (collectionHandler cmp targetSlot)
    in
    traverse_ regTarget ts
