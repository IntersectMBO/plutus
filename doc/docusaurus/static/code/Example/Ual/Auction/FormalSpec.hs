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

annotations :: ModuleUal
annotations = $(ualModule)
