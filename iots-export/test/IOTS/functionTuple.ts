// IOTSSpec.CurrencySymbol
const CurrencySymbol = t.type({
    unCurrencySymbol: t.string
});

// IOTSSpec.TokenName
const TokenName = t.type({
    unTokenName: t.string
});

const TupleFunctionArgs = t.type({
    a: t.tuple([
        CurrencySymbol,
        TokenName
    ])
});

const TupleFunctionReturn = t.string;

export const TupleFunction = createEndpoint<typeof TupleFunctionArgs, typeof TupleFunctionReturn, t.NullC>(
    'TupleFunction',
    TupleFunctionArgs,
    TupleFunctionReturn
);