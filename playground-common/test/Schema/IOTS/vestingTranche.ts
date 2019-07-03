import * as t from 'io-ts'


// Schema.IOTSSpec
const Slot = t.type({
    getSlot: t.Int
});

// Schema.IOTSSpec
const CurrencySymbol = t.type({
    unCurrencySymbol: t.string
});

// Schema.IOTSSpec
const TokenName = t.type({
    unTokenName: t.string
});

// Schema.IOTSSpec
const Value = t.type({
    getValue: t.record(CurrencySymbol, t.record(TokenName, t.Int))
});

// Schema.IOTSSpec
const IntervalSlot = t.type({
    ivFrom: t.union([
        t.null,
        Slot
    ]),
    ivTo: t.union([
        t.null,
        Slot
    ])
});

// Schema.IOTSSpec
const VestingTranche = t.type({
    vestingTrancheDate: Slot,
    vestingTrancheAmount: Value,
    validity: IntervalSlot
});
