import * as t from 'io-ts';

// IOTSSpec.CurrencySymbol
const CurrencySymbol = t.type({
    unCurrencySymbol: t.string
});

// IOTSSpec.TokenName
const TokenName = t.type({
    unTokenName: t.string
});

const TupleFunctionArgA = t.tuple([
    CurrencySymbol,
    TokenName
]);

const TupleFunctionArgReturn = t.string;

type TupleFunction = (
    a: t.TypeOf<typeof TupleFunctionArgA>
) => t.TypeOf<typeof TupleFunctionArgReturn>;
