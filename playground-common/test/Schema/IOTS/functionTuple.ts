import * as t from 'io-ts'

// Schema.IOTSSpec.CurrencySymbol
const CurrencySymbol = t.type({
    unCurrencySymbol: t.string
});

// Schema.IOTSSpec.TokenName
const TokenName = t.type({
    unTokenName: t.string
});

class Type {
    constructor(
        readonly someFunction: (
            a: t.tuple([
                CurrencySymbol,
                TokenName
            ])
        ) => t.string
    ) {}
}
