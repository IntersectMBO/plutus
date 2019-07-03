import * as t from 'io-ts'


// Schema.IOTSSpec
const ResponseString = t.union([
    t.type({UnknownError: t.tuple([
        t.Int,
        t.string
    ])}),
    t.type({StatusError: t.type({
        code: t.Int,
        message: t.string,
        metrics: t.record(t.string, t.Int)
    })}),
    t.type({Response: t.string}),
    t.literal('EmptyResponse')
]);
