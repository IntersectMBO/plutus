// IOTSSpec.CurrencySymbol
const CurrencySymbol = t.type({
    unCurrencySymbol: t.string
});

// IOTSSpec.TokenName
const TokenName = t.type({
    unTokenName: t.string
});

// IOTSSpec.AssocMap
const AssocMapTokenNameInteger = t.type({
    unMap: t.array(
        t.tuple([
            TokenName,
            t.number
        ])
    )
});

// IOTSSpec.AssocMap
const AssocMapCurrencySymbolAssocMapTokenNameInteger = t.type({
    unMap: t.array(
        t.tuple([
            CurrencySymbol,
            AssocMapTokenNameInteger
        ])
    )
});

// IOTSSpec.Value
const Value = t.type({
    getValue: AssocMapCurrencySymbolAssocMapTokenNameInteger
});

// IOTSSpec.Slot
const Slot = t.type({
    getSlot: t.number
});

// IOTSSpec.Interval
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

// IOTSSpec.VestingTranche
const VestingTranche = t.type({
    vestingTrancheDate: Slot,
    vestingTrancheAmount: Value,
    validity: IntervalSlot
});

const FunctionAArgs = t.type({
    a: t.tuple([
        CurrencySymbol,
        TokenName
    ]),
    b: t.union([
        Value,
        t.null
    ]),
    c: IntervalSlot,
    d: t.array(
        VestingTranche
    )
});

const FunctionAReturn = t.string;

export const FunctionA = createEndpoint<typeof FunctionAArgs, typeof FunctionAReturn, t.NullC>(
    'FunctionA',
    FunctionAArgs,
    FunctionAReturn
);

const FunctionBArgs = t.type({
    a: IntervalSlot,
    b: t.array(
        CurrencySymbol
    )
});

const FunctionBReturn = t.string;

export const FunctionB = createEndpoint<typeof FunctionBArgs, typeof FunctionBReturn, t.NullC>(
    'FunctionB',
    FunctionBArgs,
    FunctionBReturn
);