import * as t from 'io-ts';

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
            t.Int
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
    getSlot: t.Int
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

const FunctionAArgA = t.tuple([
    CurrencySymbol,
    TokenName
]);

const FunctionAArgB = t.union([
    Value,
    t.null
]);

const FunctionAArgC = IntervalSlot;

const FunctionAArgD = t.array(
    VestingTranche
);

const FunctionAArgReturn = t.string;

type FunctionA = (
    a: t.TypeOf<typeof FunctionAArgA>,
    b: t.TypeOf<typeof FunctionAArgB>,
    c: t.TypeOf<typeof FunctionAArgC>,
    d: t.TypeOf<typeof FunctionAArgD>
) => t.TypeOf<typeof FunctionAArgReturn>;

const FunctionBArgA = IntervalSlot;

const FunctionBArgB = t.array(
    CurrencySymbol
);

const FunctionBArgReturn = t.string;

type FunctionB = (
    a: t.TypeOf<typeof FunctionBArgA>,
    b: t.TypeOf<typeof FunctionBArgB>
) => t.TypeOf<typeof FunctionBArgReturn>;
