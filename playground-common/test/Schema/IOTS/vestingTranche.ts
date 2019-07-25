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

// io-ts methods return values, not TS type definitions.
// This is by design, values have the `decode` property for
// runtime validation, and allows the values to be useful in
// JS land. This is what we'll run on the client
const functionArgA = t.tuple([
    CurrencySymbol,
    TokenName
])

const functionArgB = t.union([
    Value,
    t.null
])

const functionArgC = IntervalSlot
const functionArgD = t.array(VestingTranche)
const functionReturnType = t.string

// We can use the above values for runtime validation,
// but for TS users during development, we do the following:
type SomeFunction = (
    a: t.TypeOf<typeof functionArgA>,
    b: t.TypeOf<typeof functionArgB>,
    c: t.TypeOf<typeof functionArgC>,
    d: t.TypeOf<typeof functionArgD>,
) => t.TypeOf<typeof functionReturnType>