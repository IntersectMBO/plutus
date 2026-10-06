{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Example.Ual.Auction.FormalSpec (annotations) where

import Example.Ual.Auction.OnChain (auction, outbids)
import PlutusTx.Prelude (BuiltinData, BuiltinUnit)
import PlutusTx.Ual (ModuleUal)
import PlutusTx.Ual.TH (ualModule)

-- This module imports implementation bindings. It contains no on-chain code.
{-@ ONCHAIN [kind: script] [version: PlutusV3] [steps: 10000, semantics: E]
    auction :: BuiltinData -> BuiltinUnit
@-}
{-@ ONCHAIN [kind: function] [version: PlutusV3] [steps: 100, semantics: E]
    outbids :: { Integer : asNative } -> { Integer : asNative } -> { Bool : asNative }
@-}

{-@ PREDICATE
  def typedAuction (validator : Data → State) (ctx : CardanoLedgerApi.V3.Contexts.ScriptContext) :=
    validator (CardanoLedgerApi.IsData.Class.IsData.toData ctx)

  def bidScenario (validator : Data → State) (old proposed locked refund tokens hi : Integer) :=
    typedAuction validator (CardanoLedgerApi.Examples.Auction.newBidContext old proposed locked refund tokens hi)

  def payoutScenario (validator : Data → State) (bid paid tokens lo : Integer) :=
    typedAuction validator (CardanoLedgerApi.Examples.Auction.payoutContext bid paid tokens lo)
@-}

{-@ PROPERTY [scope: outbids] outbids_exact
    "The separately compiled helper returns the native comparison result."
  : ∀ (old proposed : Integer), outbids_returns old proposed (decide (old < proposed))
@-}
{-@ PROPERTY [scope: auction] first_bid_exact
    "For the upstream no-previous-bid scenario, the minimum, deadline, locked Ada and NFT quantity characterize success."
  : ∀ (proposed locked tokens hi : Integer),
      isSuccessful (bidScenario auction 0 proposed locked 0 tokens hi) ↔
        100 ≤ proposed ∧ hi ≤ 1725227091000 ∧ locked = proposed ∧ tokens = 1
@-}
{-@ PROPERTY [scope: auction] existing_bid_exact
    "For a positive previous bid, success requires a strictly larger bid, exact refund, correct continuing value and the deadline."
  : ∀ (old proposed locked refund tokens hi : Integer), 0 < old →
      (isSuccessful (bidScenario auction old proposed locked refund tokens hi) ↔
        old < proposed ∧ hi ≤ 1725227091000 ∧ locked = proposed ∧ refund = old ∧ tokens = 1)
@-}
{-@ PROPERTY [scope: auction] payout_exact
    "For the upstream payout scenario, the deadline, NFT and seller payment characterize success."
  : ∀ (bid paid tokens lo : Integer),
      isSuccessful (payoutScenario auction bid paid tokens lo) ↔
        1725227091000 ≤ lo ∧ tokens = 1 ∧ (0 < bid → paid = bid)
@-}
{-@ PROPERTY [scope: auction] malformed_context
    "An integer is not a V3 ScriptContext and is rejected."
  : ∀ (n : Integer), isUnsuccessful (auction (Data.I n))
@-}

{-@ PREDICATE
  def auditBid (validator : Data → State) (old proposed locked refund tokens hi : Integer) : Prop :=
    isSuccessful (bidScenario validator old proposed locked refund tokens hi)
  def auditPayout (validator : Data → State) (bid paid tokens lo : Integer) : Prop :=
    isSuccessful (payoutScenario validator bid paid tokens lo)
  def auditAttack (validator : Data → State) (old proposed locked refund tokens hi junk minted : Integer) : Prop :=
    isSuccessful (typedAuction validator (CardanoLedgerApi.Examples.Auction.newBidAttackContext old proposed locked refund tokens hi junk minted))
  def auditDouble (validator : Data → State) (bid paid tokens lo : Integer) : Prop :=
    isSuccessful (typedAuction validator (CardanoLedgerApi.Examples.Auction.payoutDoubleSatContext bid paid tokens lo))
  def auditAccepts (validator : Data → State) (ctx : CardanoLedgerApi.V3.Contexts.ScriptContext) : Prop :=
    isSuccessful (typedAuction validator ctx)
@-}

{-@ PROPERTY [scope: auction] audit_newBid_success_requires_sufficient_bid
    "Upstream Auction audit: newBid_success_requires_sufficient_bid. Checked against this freshly compiled program."
  : ∀ (newBidAmt outAda outTok hi : Integer),
    auditBid auction 0 newBidAmt outAda 0 outTok hi
    → CardanoLedgerApi.Examples.Auction.bakedMinBid ≤ newBidAmt
@-}

{-@ PROPERTY [scope: auction] audit_newBid_success_requires_bigger_bid
    "Upstream Auction audit: newBid_success_requires_bigger_bid. Checked against this freshly compiled program."
  : ∀ (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer),
    auditBid auction oldBidAmt newBidAmt outAda refundAda outTok hi
    → oldBidAmt < newBidAmt
@-}

{-@ PROPERTY [scope: auction] audit_newBid_success_requires_before_deadline
    "Upstream Auction audit: newBid_success_requires_before_deadline. Checked against this freshly compiled program."
  : ∀ (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer),
    auditBid auction oldBidAmt newBidAmt outAda refundAda outTok hi
    → hi ≤ CardanoLedgerApi.Examples.Auction.bakedEndTime
@-}

{-@ PROPERTY [scope: auction] audit_newBid_success_requires_output_locks_bid
    "Upstream Auction audit: newBid_success_requires_output_locks_bid. Checked against this freshly compiled program."
  : ∀ (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer),
    auditBid auction oldBidAmt newBidAmt outAda refundAda outTok hi
    → outAda = newBidAmt
@-}

{-@ PROPERTY [scope: auction] audit_newBid_success_requires_single_nft
    "Upstream Auction audit: newBid_success_requires_single_nft. Checked against this freshly compiled program."
  : ∀ (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer),
    auditBid auction oldBidAmt newBidAmt outAda refundAda outTok hi
    → outTok = 1
@-}

{-@ PROPERTY [scope: auction] audit_valid_newBid_succeeds
    "Upstream Auction audit: valid_newBid_succeeds. Checked against this freshly compiled program."
  : ∀ (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer),
    CardanoLedgerApi.Examples.Auction.bakedMinBid ≤ newBidAmt →
    oldBidAmt < newBidAmt   →
    hi ≤ CardanoLedgerApi.Examples.Auction.bakedEndTime       →
    outAda = newBidAmt      →
    refundAda = oldBidAmt   →
    outTok = 1
    → auditBid auction oldBidAmt newBidAmt outAda refundAda outTok hi
@-}

{-@ PROPERTY [scope: auction] audit_newBid_accepts_minimal_increment
    "Upstream Auction audit: newBid_accepts_minimal_increment. Checked against this freshly compiled program."
  : ∀ (oldBidAmt outAda refundAda outTok hi : Integer),
    CardanoLedgerApi.Examples.Auction.bakedMinBid ≤ oldBidAmt + 1 →
    hi ≤ CardanoLedgerApi.Examples.Auction.bakedEndTime          →
    outAda = oldBidAmt + 1     →
    refundAda = oldBidAmt      →
    outTok = 1
    → auditBid auction oldBidAmt (oldBidAmt + 1) outAda refundAda outTok hi
@-}

{-@ PROPERTY [scope: auction] audit_payout_success_requires_after_deadline
    "Upstream Auction audit: payout_success_requires_after_deadline. Checked against this freshly compiled program."
  : ∀ (bidAmt sellerAda assetTok lo : Integer),
    auditPayout auction bidAmt sellerAda assetTok lo
    → CardanoLedgerApi.Examples.Auction.bakedEndTime ≤ lo
@-}

{-@ PROPERTY [scope: auction] audit_payout_success_pays_seller_highest_bid
    "Upstream Auction audit: payout_success_pays_seller_highest_bid. Checked against this freshly compiled program."
  : ∀ (bidAmt sellerAda assetTok lo : Integer),
    auditPayout auction bidAmt sellerAda assetTok lo →
    0 < bidAmt
    → sellerAda = bidAmt
@-}

{-@ PROPERTY [scope: auction] audit_payout_success_transfers_asset
    "Upstream Auction audit: payout_success_transfers_asset. Checked against this freshly compiled program."
  : ∀ (bidAmt sellerAda assetTok lo : Integer),
    auditPayout auction bidAmt sellerAda assetTok lo
    → assetTok = 1
@-}

{-@ PROPERTY [scope: auction] audit_valid_payout_with_bid_succeeds
    "Upstream Auction audit: valid_payout_with_bid_succeeds. Checked against this freshly compiled program."
  : ∀ (bidAmt sellerAda assetTok lo : Integer),
    0 < bidAmt         →
    CardanoLedgerApi.Examples.Auction.bakedEndTime ≤ lo  →
    sellerAda = bidAmt →
    assetTok = 1
    → auditPayout auction bidAmt sellerAda assetTok lo
@-}

{-@ PROPERTY [scope: auction] audit_valid_payout_no_bid_succeeds
    "Upstream Auction audit: valid_payout_no_bid_succeeds. Checked against this freshly compiled program."
  : ∀ (sellerAda assetTok lo : Integer),
    CardanoLedgerApi.Examples.Auction.bakedEndTime ≤ lo →
    assetTok = 1
    → auditPayout auction 0 sellerAda assetTok lo
@-}

{-@ PROPERTY [scope: auction] audit_newBid_accepts_dust_tokens
    "Upstream Auction audit: newBid_accepts_dust_tokens. Checked against this freshly compiled program."
  : ∀ (oldBidAmt newBidAmt outAda refundAda outTok hi junkTok : Integer),
    CardanoLedgerApi.Examples.Auction.bakedMinBid ≤ newBidAmt →
    oldBidAmt < newBidAmt   →
    hi ≤ CardanoLedgerApi.Examples.Auction.bakedEndTime       →
    outAda = newBidAmt      →
    refundAda = oldBidAmt   →
    outTok = 1
    → auditAttack auction oldBidAmt newBidAmt outAda refundAda outTok hi junkTok 0
@-}

{-@ PROPERTY [scope: auction] audit_newBid_ignores_minting
    "Upstream Auction audit: newBid_ignores_minting. Checked against this freshly compiled program."
  : ∀ (oldBidAmt newBidAmt outAda refundAda outTok hi mintTok : Integer),
    CardanoLedgerApi.Examples.Auction.bakedMinBid ≤ newBidAmt →
    oldBidAmt < newBidAmt   →
    hi ≤ CardanoLedgerApi.Examples.Auction.bakedEndTime       →
    outAda = newBidAmt      →
    refundAda = oldBidAmt   →
    outTok = 1
    → auditAttack auction oldBidAmt newBidAmt outAda refundAda outTok hi 0 mintTok
@-}

{-@ PROPERTY [scope: auction] audit_payout_double_satisfaction
    "Upstream Auction audit: payout_double_satisfaction. Checked against this freshly compiled program."
  : ∀ (bidAmt sellerAda assetTok lo : Integer),
    0 < bidAmt         →
    CardanoLedgerApi.Examples.Auction.bakedEndTime ≤ lo  →
    sellerAda = bidAmt →
    assetTok = 1
    → auditDouble auction bidAmt sellerAda assetTok lo
@-}

{-@ PROPERTY [scope: auction] audit_newBid_success_positive_bid
    "Upstream Auction audit: newBid_success_positive_bid. Checked against this freshly compiled program."
  : ∀ (oldBidAmt newBidAmt outAda refundAda outTok hi : Integer),
    auditBid auction oldBidAmt newBidAmt outAda refundAda outTok hi
    → 0 < newBidAmt
@-}

{-@ PROPERTY [scope: auction] audit_payout_success_positive_asset
    "Upstream Auction audit: payout_success_positive_asset. Checked against this freshly compiled program."
  : ∀ (bidAmt sellerAda assetTok lo : Integer),
    auditPayout auction bidAmt sellerAda assetTok lo
    → 0 < assetTok
@-}

{-@ PROPERTY [scope: auction] audit_payout_success_positive_seller_payment
    "Upstream Auction audit: payout_success_positive_seller_payment. Checked against this freshly compiled program."
  : ∀ (bidAmt sellerAda assetTok lo : Integer),
    auditPayout auction bidAmt sellerAda assetTok lo →
    0 < bidAmt
    → 0 < sellerAda
@-}

{-@ PROPERTY [scope: auction] audit_demo_valid_bid_accepted
    "Upstream Auction audit: demo_valid_bid_accepted. Checked against this freshly compiled program."
  : auditAccepts auction CardanoLedgerApi.Examples.Auction.demoValidCtx
@-}

{-@ PROPERTY [scope: auction] audit_nb_wrong_token_name_rejected
    "Upstream Auction audit: nb_wrong_token_name_rejected. Checked against this freshly compiled program."
  : ¬ auditAccepts auction CardanoLedgerApi.Examples.Auction.demoWrongTnCtx
@-}

{-@ PROPERTY [scope: auction] audit_nb_wrong_policy_rejected
    "Upstream Auction audit: nb_wrong_policy_rejected. Checked against this freshly compiled program."
  : ¬ auditAccepts auction CardanoLedgerApi.Examples.Auction.demoWrongPolicyCtx
@-}

{-@ PROPERTY [scope: auction] audit_nb_datum_hash_rejected
    "Upstream Auction audit: nb_datum_hash_rejected. Checked against this freshly compiled program."
  : ¬ auditAccepts auction CardanoLedgerApi.Examples.Auction.demoDatumHashCtx
@-}

{-@ PROPERTY [scope: auction] audit_nb_datum_missing_rejected
    "Upstream Auction audit: nb_datum_missing_rejected. Checked against this freshly compiled program."
  : ¬ auditAccepts auction CardanoLedgerApi.Examples.Auction.demoNoDatumCtx
@-}

{-@ PROPERTY [scope: auction] audit_nb_datum_wrong_bid_rejected
    "Upstream Auction audit: nb_datum_wrong_bid_rejected. Checked against this freshly compiled program."
  : ¬ auditAccepts auction CardanoLedgerApi.Examples.Auction.demoWrongDatumCtx
@-}

{-@ PROPERTY [scope: auction] audit_nb_other_redeemer_rejected
    "Upstream Auction audit: nb_other_redeemer_rejected. Checked against this freshly compiled program."
  : ¬ auditAccepts auction CardanoLedgerApi.Examples.Auction.demoOtherRedeemerCtx
@-}

{-@ PROPERTY [scope: auction] audit_payout_staked_outputs_accepted
    "Upstream Auction audit: payout_staked_outputs_accepted. Checked against this freshly compiled program."
  : auditAccepts auction CardanoLedgerApi.Examples.Auction.demoPayoutStakedCtx
@-}

annotations :: ModuleUal
annotations = $(ualModule)
