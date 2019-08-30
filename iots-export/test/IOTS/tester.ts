// Ledger.Value
const CurrencySymbol = t.type({
    unCurrencySymbol: t.string
});

// Ledger.Slot
const Slot = t.type({
    getSlot: t.number
});

// Ledger.Crypto
const PubKey = t.type({
    getPubKey: t.string
});

// Ledger.Value
const TokenName = t.type({
    unTokenName: t.string
});

// Ledger.Value
const Value = t.type({
    getValue: t.record(
        CurrencySymbol,
        t.record(
            TokenName,
            t.number
        )
    )
});

// Main
const Campaign = t.type({
    campaignDeadline: Slot,
    campaignTarget: Value,
    campaignCollectionDeadline: Slot,
    campaignOwner: PubKey
});

// Main
const CampaignAction = t.union([
    t.literal('Collect'),
    t.literal('Refund')
]);
