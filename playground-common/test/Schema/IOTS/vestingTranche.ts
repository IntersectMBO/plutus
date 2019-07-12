import * as t from 'io-ts'

// Schema.IOTSSpec.CurrencySymbol
const CurrencySymbol = t.type({
    unCurrencySymbol: t.string
});

// Schema.IOTSSpec.TokenName
const TokenName = t.type({
    unTokenName: t.string
});

// Schema.IOTSSpec.AssocMap
const AssocMapTokenNameInteger = t.type({
    unMap: t.array(t.tuple([
        TokenName,
        t.Int
    ]))
});

// Schema.IOTSSpec.AssocMap
const AssocMapCurrencySymbolAssocMapTokenNameInteger = t.type({
    unMap: t.array(t.tuple([
        CurrencySymbol,
        AssocMapTokenNameInteger
    ]))
});

// Schema.IOTSSpec.Value
const Value = t.type({
    getValue: AssocMapCurrencySymbolAssocMapTokenNameInteger
});

// Schema.IOTSSpec.Slot
const Slot = t.type({
    getSlot: t.Int
});

// Schema.IOTSSpec.Interval
const IntervalSlot = t.type({
    ivFrom: t.union([
        Slot,
        t.null
    ]),
    ivTo: t.union([
        Slot,
        t.null
    ])
});

// Schema.IOTSSpec.VestingTranche
const VestingTranche = t.type({
    vestingTrancheDate: Slot,
    vestingTrancheAmount: Value,
    validity: IntervalSlot
});

class Type {
    constructor(
        readonly someFunction: (
            a: t.tuple([
                CurrencySymbol,
                TokenName
            ]),
            b: t.union([
                Value,
                t.null
            ]),
            c: IntervalSlot,
            d: t.array(VestingTranche)
        ) => t.string
    ) {}
}
